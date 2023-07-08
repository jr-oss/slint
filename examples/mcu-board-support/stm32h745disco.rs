// Copyright © SixtyFPS GmbH <info@slint.dev>
// SPDX-License-Identifier: MIT

extern crate alloc;

use alloc::boxed::Box;
use alloc::rc::Rc;
use core::cell::RefCell;
pub use cortex_m_rt::entry;
use defmt_rtt as _;
use embedded_display_controller::{DisplayController, DisplayControllerLayer};
use hal::delay::Delay;
use hal::gpio::Speed;
use hal::pac;
use hal::prelude::*;
use slint::platform::software_renderer;
use stm32h7xx_hal as hal; // global logger

#[cfg(feature = "panic-probe")]
use panic_probe as _;

use embedded_alloc::LlffHeap as Heap;


/// Configre a pin for the FMC controller
macro_rules! fmc_pins {
    ($($pin:expr),*) => {
        (
            $(
                $pin.into_push_pull_output()
                    .speed(Speed::VeryHigh)
                    .into_alternate::<12>()
                    .internal_pull_up(true)
            ),*
        )
    };
}

const HEAP_SIZE: usize = 200 * 1024;
static mut HEAP: [u8; HEAP_SIZE] = [0; HEAP_SIZE];

const DISPLAY_WIDTH: usize = 480;
const DISPLAY_HEIGHT: usize = 272;

/// The Pixel type of the backing store
pub type TargetPixel = software_renderer::Rgb565Pixel;

#[global_allocator]
static ALLOCATOR: Heap = Heap::empty();

static RNG: cortex_m::interrupt::Mutex<core::cell::RefCell<Option<hal::rng::Rng>>> =
    cortex_m::interrupt::Mutex::new(core::cell::RefCell::new(None));

pub fn init() {
    unsafe { ALLOCATOR.init(&mut HEAP as *const u8 as usize, core::mem::size_of_val(&HEAP)) }
    slint::platform::set_platform(Box::new(StmBackend::default()))
        .expect("backend already initialized");
}

#[link_section = ".frame_buffer"]
static mut FB1: [TargetPixel; DISPLAY_WIDTH * DISPLAY_HEIGHT] =
    [software_renderer::Rgb565Pixel(0); DISPLAY_WIDTH * DISPLAY_HEIGHT];
#[link_section = ".frame_buffer"]
static mut FB2: [TargetPixel; DISPLAY_WIDTH * DISPLAY_HEIGHT] =
    [software_renderer::Rgb565Pixel(0); DISPLAY_WIDTH * DISPLAY_HEIGHT];

struct StmBackendInner {
    scb: cortex_m::peripheral::SCB,
    delay: stm32h7xx_hal::delay::Delay,
    layer: stm32h7xx_hal::ltdc::LtdcLayer1,
    touch_i2c: stm32h7xx_hal::i2c::I2c<stm32h7xx_hal::device::I2C4>,
}

struct StmBackend {
    window: RefCell<Option<Rc<slint::platform::software_renderer::MinimalSoftwareWindow>>>,
    timer: hal::timer::Timer<pac::TIM2>,
    inner: RefCell<StmBackendInner>,
}

impl Default for StmBackend {
    fn default() -> Self {
        let mut cp = cortex_m::Peripherals::take().unwrap();
        let dp = pac::Peripherals::take().unwrap();

        let pwr = dp.PWR.constrain();
        let pwrcfg = pwr.smps().freeze();
        let rcc = dp.RCC.constrain();
        let ccdr = rcc
            .sys_ck(400.MHz())
            // numbers adapted from Drivers/BSP/STM32H735G-DK/stm32h735g_discovery_ospi.c
            // MX_OSPI_ClockConfig
            .pll2_p_ck(400.MHz() / 5)
            .pll2_q_ck(400.MHz() / 2)
            .pll2_r_ck(400.MHz() / 2)
            // numbers adapted from Drivers/BSP/STM32H735G-DK/stm32h735g_discovery_lcd.c
            // MX_LTDC_ClockConfig
            .pll3_p_ck(800.MHz() / 2)
            .pll3_q_ck(800.MHz() / 2)
            .pll3_r_ck(800.MHz() / 83)
            .hclk(400.MHz() / 2)
            .freeze(pwrcfg, &dp.SYSCFG);
        let _pll3_r = ccdr.clocks.pll3_r_ck().expect("pll3 must run!");

        assert_eq!(ccdr.clocks.hclk(), 200.MHz::<1, 1>());

        let mut delay = Delay::new(cp.SYST, ccdr.clocks);

        cp.SCB.invalidate_icache();
        cp.SCB.enable_icache();
        cp.SCB.enable_dcache(&mut cp.CPUID);
        cp.DWT.enable_cycle_counter();

        let _gpioa = dp.GPIOA.split(ccdr.peripheral.GPIOA);
        let gpiob = dp.GPIOB.split(ccdr.peripheral.GPIOB);
        let _gpioc = dp.GPIOC.split(ccdr.peripheral.GPIOC);
        let gpiod = dp.GPIOD.split(ccdr.peripheral.GPIOD);
        let gpioe = dp.GPIOE.split(ccdr.peripheral.GPIOE);
        let gpiof = dp.GPIOF.split(ccdr.peripheral.GPIOF);
        let gpiog = dp.GPIOG.split(ccdr.peripheral.GPIOG);
        let gpioh = dp.GPIOH.split(ccdr.peripheral.GPIOH);
        let gpioi = dp.GPIOI.split(ccdr.peripheral.GPIOI);
        let gpioj = dp.GPIOJ.split(ccdr.peripheral.GPIOJ);
        let gpiok = dp.GPIOK.split(ccdr.peripheral.GPIOK);

        let _tracweswo = gpiob.pb3.into_alternate::<0>();

        // ----------------------------------------------------------
        // SDRAM
        // Initialise SDRAM...
        let sdram_size = 16 * 1024 * 1024 / 2; // Only half is usable

        config_mpu(&cp.MPU, &cp.SCB, sdram_size);

        let sdram_pins = fmc_pins! {
            // A0-A11
            gpiof.pf0, gpiof.pf1, gpiof.pf2, gpiof.pf3,
            gpiof.pf4, gpiof.pf5, gpiof.pf12, gpiof.pf13,
            gpiof.pf14, gpiof.pf15, gpiog.pg0, gpiog.pg1,
            // BA0-BA1
            gpiog.pg4, gpiog.pg5,
            // D0-D31
            gpiod.pd14, gpiod.pd15, gpiod.pd0, gpiod.pd1,
            gpioe.pe7, gpioe.pe8, gpioe.pe9, gpioe.pe10,
            gpioe.pe11, gpioe.pe12, gpioe.pe13, gpioe.pe14,
            gpioe.pe15, gpiod.pd8, gpiod.pd9, gpiod.pd10,

            /*gpioh.ph8, gpioh.ph9, gpioh.ph10, gpioh.ph11,
            gpioh.ph12, gpioh.ph13, gpioh.ph14, gpioh.ph15,
            gpioi.pi0, gpioi.pi1, gpioi.pi2, gpioi.pi3,
            gpioi.pi6, gpioi.pi7, gpioi.pi9, gpioi.pi10,*/
            // NBL0 - NBL3
            gpioe.pe0, gpioe.pe1, /*gpioi.pi4, gpioi.pi5,*/
            gpioh.ph7,              // SDCKE1
            gpiog.pg8,              // SDCLK
            gpiog.pg15,             // SDNCAS
            gpioh.ph6,              // SDNE1 (!CS)
            gpiof.pf11,             // SDRAS
            gpioh.ph5               // SDNWE
        };

        // sdram_device.
        let mut sdram = dp.FMC.sdram(
            sdram_pins,
            // mt48lc4m32b2_6::Mt48lc4m32b2 {},
            mt48lc4m32b2_16_6::Mt48lc4m32b2_16 {},
            ccdr.peripheral.FMC,
            &ccdr.clocks,
        );
        let sdram_base = sdram.init(&mut delay);

        // SAFETY the init function is only called once (as enforced by Peripherals::take)
        let (fb1, fb2) = { (ptr::addr_of_mut!(FB1), ptr::addr_of_mut!(FB2)) };
        // Make sure, that init returns same memory address as defined in memory.x
        assert_eq!(sdram_base as usize, fb1.as_ptr() as *const TargetPixel as usize);
        fb1.fill(slint::platform::software_renderer::Rgb565Pixel(0));
        fb2.fill(slint::platform::software_renderer::Rgb565Pixel(0));

        // setup LTDC  (LTDC_MspInit)
        let _p = gpioh.ph9.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioi.pi0.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioi.pi1.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioi.pi9.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioi.pi12.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioi.pi14.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioi.pi15.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj0.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj1.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj3.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj4.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj5.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj6.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj7.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj8.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj9.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj10.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj11.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj12.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj13.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj14.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpioj.pj15.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpiok.pk2.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpiok.pk3.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpiok.pk4.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpiok.pk5.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpiok.pk6.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);
        let _p = gpiok.pk7.into_alternate::<14>().speed(Speed::High).internal_pull_up(true);

        //let mut lcd_disp_en = gpiok.pk7.into_push_pull_output();
        let mut lcd_disp_ctrl = gpiod.pd7.into_push_pull_output();
        let mut lcd_bl_ctrl = gpiok.pk0.into_push_pull_output();

        delay.delay_ms(40u8);
        // End LTDC_MspInit

        let mut ltdc = hal::ltdc::Ltdc::new(dp.LTDC, ccdr.peripheral.LTDC, &ccdr.clocks);

        const RK043FN48H_HSYNC: u16 = 41; /* Horizontal synchronization */
        const RK043FN48H_HBP: u16 = 13; /* Horizontal back porch      */
        const RK043FN48H_HFP: u16 = 32; /* Horizontal front porch     */
        const RK043FN48H_VSYNC: u16 = 10; /* Vertical synchronization   */
        const RK043FN48H_VBP: u16 = 2; /* Vertical back porch        */
        const RK043FN48H_VFP: u16 = 2; /* Vertical front porch       */

        ltdc.init(embedded_display_controller::DisplayConfiguration {
            active_width: DISPLAY_WIDTH as _,
            active_height: DISPLAY_HEIGHT as _,
            h_back_porch: RK043FN48H_HBP - 11, // -11 from MX_LTDC_Init
            h_front_porch: RK043FN48H_HFP,
            v_back_porch: RK043FN48H_VBP,
            v_front_porch: RK043FN48H_VFP,
            h_sync: RK043FN48H_HSYNC,
            v_sync: RK043FN48H_VSYNC,
            h_sync_pol: false,
            v_sync_pol: false,
            not_data_enable_pol: false,
            pixel_clock_pol: false,
        });
        let mut layer = ltdc.split();

        // Safety: the frame buffer has the right size
        unsafe {
            layer.enable(
                fb1.as_ptr() as *const u8,
                embedded_display_controller::PixelFormat::RGB565,
            );
        }

        //lcd_disp_en.set_low();
        lcd_disp_ctrl.set_high();
        lcd_bl_ctrl.set_high();

        // Init Timer
        let mut timer = dp.TIM2.tick_timer(10000.Hz(), ccdr.peripheral.TIM2, &ccdr.clocks);
        timer.listen(hal::timer::Event::TimeOut);

        // Init RNG
        let rng = dp.RNG.constrain(ccdr.peripheral.RNG, &ccdr.clocks);
        cortex_m::interrupt::free(|cs| {
            let _ = RNG.borrow(cs).replace(Some(rng));
        });

        // Init Touch screen
        let scl = gpiod.pd12.into_alternate_open_drain().speed(Speed::High).internal_pull_up(true);
        let sda = gpiod.pd13.into_alternate_open_drain().speed(Speed::High).internal_pull_up(true);
        let touch_i2c = dp.I2C4.i2c((scl, sda), 100u32.kHz(), ccdr.peripheral.I2C4, &ccdr.clocks);

        Self {
            window: RefCell::default(),
            timer,
            inner: RefCell::new(StmBackendInner { scb: cp.SCB, delay, layer, touch_i2c }),
        }
    }
}

impl slint::platform::Platform for StmBackend {
    fn create_window_adapter(
        &self,
    ) -> Result<Rc<dyn slint::platform::WindowAdapter>, slint::PlatformError> {
        let window = slint::platform::software_renderer::MinimalSoftwareWindow::new(
            slint::platform::software_renderer::RepaintBufferType::SwappedBuffers,
        );
        self.window.replace(Some(window.clone()));
        Ok(window)
    }

    fn run_event_loop(&self) -> Result<(), slint::PlatformError> {
        let inner = &mut *self.inner.borrow_mut();

        let mut ft5336 =
            ft5336::Ft5336::new(&mut inner.touch_i2c, 0x70 >> 1, &mut inner.delay).unwrap();
        ft5336.init(&mut inner.touch_i2c);

        // Safety: The Refcell at the beginning of `run_event_loop` prevents re-entrancy and thus multiple mutable references to FB1/FB2.
        let (fb1, fb2) = { (ptr::addr_of_mut!(FB1), ptr::addr_of_mut!(FB2)) };

        let mut displayed_fb: &mut [TargetPixel] = fb1;
        let mut work_fb: &mut [TargetPixel] = fb2;

        let mut last_touch = None;
        self.window
            .borrow()
            .as_ref()
            .unwrap()
            .set_size(slint::PhysicalSize::new(DISPLAY_WIDTH as u32, DISPLAY_HEIGHT as u32));
        loop {
            slint::platform::update_timers_and_animations();

            if let Some(window) = self.window.borrow().clone() {
                window.draw_if_needed(|renderer| {
                    while inner.layer.is_swap_pending() {}
                    renderer.render(work_fb, DISPLAY_WIDTH);
                    inner.scb.clean_dcache_by_slice(work_fb);
                    // Safety: the frame buffer has the right size
                    unsafe { inner.layer.swap_framebuffer(work_fb.as_ptr() as *const u8) };
                    // Swap the buffer pointer so we will work now on the second buffer
                    core::mem::swap::<&mut [_]>(&mut work_fb, &mut displayed_fb);
                });

                // handle touch event
                let touch = ft5336.detect_touch(&mut inner.touch_i2c).unwrap();
                let button = slint::platform::PointerEventButton::Left;
                let event = if touch > 0 {
                    let state = ft5336.get_touch(&mut inner.touch_i2c, 1).unwrap();
                    let position = slint::PhysicalPosition::new(state.y as i32, state.x as i32)
                        .to_logical(window.scale_factor());
                    Some(match last_touch.replace(position) {
                        Some(_) => slint::platform::WindowEvent::PointerMoved { position },
                        None => slint::platform::WindowEvent::PointerPressed { position, button },
                    })
                } else {
                    last_touch.take().map(|position| {
                        slint::platform::WindowEvent::PointerReleased { position, button }
                    })
                };

                if let Some(event) = event {
                    let is_pointer_release_event =
                        matches!(event, slint::platform::WindowEvent::PointerReleased { .. });

                    window.dispatch_event(event);

                    // removes hover state on widgets
                    if is_pointer_release_event {
                        window.dispatch_event(slint::platform::WindowEvent::PointerExited);
                    }
                }
            }

            // FIXME: cortex_m::asm::wfe();
        }
    }

    fn duration_since_start(&self) -> core::time::Duration {
        // FIXME! the timer can overflow
        let val = self.timer.counter() / 10;
        core::time::Duration::from_millis(val.into())
    }

    fn debug_log(&self, arguments: core::fmt::Arguments) {
        use alloc::string::ToString;
        defmt::println!("{=str}", arguments.to_string());
    }
}

fn rng(buf: &mut [u8]) -> Result<(), getrandom::Error> {
    cortex_m::interrupt::free(|cs| match RNG.borrow(cs).borrow_mut().as_mut() {
        Some(rng) => rng.fill(buf).map_err(|e| match e {
            stm32h7xx_hal::rng::ErrorKind::ClockError => getrandom::Error::UNSUPPORTED,
            stm32h7xx_hal::rng::ErrorKind::SeedError => getrandom::Error::UNSUPPORTED,
        }),
        None => Err(getrandom::Error::UNSUPPORTED),
    })
}

getrandom::register_custom_getrandom!(rng);

fn config_mpu(mpu: &cortex_m::peripheral::MPU, scb: &cortex_m::peripheral::SCB, size: usize) {
    // let mpu = cp.MPU;
    // let scb = &mut cp.SCB;
    // let size = sdram_size;
    // Refer to ARM®v7-M Architecture Reference Manual ARM DDI 0403
    // Version E.b Section B3.5
    const MEMFAULTENA: u32 = 1 << 16;

    unsafe {
        /* Make sure outstanding transfers are done */
        cortex_m::asm::dmb();

        scb.shcsr.modify(|r| r & !MEMFAULTENA);

        /* Disable the MPU and clear the control register*/
        mpu.ctrl.write(0);
    }

    const REGION_NUMBER0: u32 = 0x00;
    const REGION_BASE_ADDRESS: u32 = 0xD000_0000;

    const REGION_FULL_ACCESS: u32 = 0x03;
    const REGION_CACHEABLE: u32 = 0x01;
    const REGION_WRITE_BACK: u32 = 0x01;
    const REGION_ENABLE: u32 = 0x01;

    assert_eq!(size & (size - 1), 0, "SDRAM memory region size must be a power of 2");
    assert_eq!(size & 0x1F, 0, "SDRAM memory region size must be 32 bytes or more");
    fn log2minus1(sz: u32) -> u32 {
        for i in 5..=31 {
            if sz == (1 << i) {
                return i - 1;
            }
        }
        panic!("Unknown SDRAM memory region size!");
    }

    // info!("SDRAM Memory Size 0x{:x}", log2minus1(size as u32));

    // Configure region 0
    //
    // Cacheable, outer and inner write-back, no write allocate. So
    // reads are cached, but writes always write all the way to SDRAM
    unsafe {
        mpu.rnr.write(REGION_NUMBER0);
        mpu.rbar.write(REGION_BASE_ADDRESS);
        mpu.rasr.write(
            (REGION_FULL_ACCESS << 24)
                | (REGION_CACHEABLE << 17)
                | (REGION_WRITE_BACK << 16)
                | (log2minus1(size as u32) << 1)
                | REGION_ENABLE,
        );
    }

    const MPU_ENABLE: u32 = 0x01;
    const MPU_DEFAULT_MMAP_FOR_PRIVILEGED: u32 = 0x04;

    // Enable
    unsafe {
        mpu.ctrl.modify(|r| r | MPU_DEFAULT_MMAP_FOR_PRIVILEGED | MPU_ENABLE);

        scb.shcsr.modify(|r| r | MEMFAULTENA);

        // Ensure MPU settings take effect
        cortex_m::asm::dsb();
        cortex_m::asm::isb();
    }
}

/// Micron MT48LC4M32B2 SDRAM
#[allow(unused)]
/// Speed Grade 6
pub mod mt48lc4m32b2_16_6 {
    use stm32_fmc::{SdramChip, SdramConfiguration, SdramTiming};

    const BURST_LENGTH_1: u16 = 0x0000;
    const BURST_LENGTH_2: u16 = 0x0001;
    const BURST_LENGTH_4: u16 = 0x0002;
    const BURST_LENGTH_8: u16 = 0x0004;
    const BURST_TYPE_SEQUENTIAL: u16 = 0x0000;
    const BURST_TYPE_INTERLEAVED: u16 = 0x0008;
    const CAS_LATENCY_2: u16 = 0x0020;
    const CAS_LATENCY_3: u16 = 0x0030;
    const OPERATING_MODE_STANDARD: u16 = 0x0000;
    const WRITEBURST_MODE_PROGRAMMED: u16 = 0x0000;
    const WRITEBURST_MODE_SINGLE: u16 = 0x0200;

    /// MT48LC4M32B2 with Speed Grade 6
    #[derive(Clone, Copy, Debug, PartialEq)]
    pub struct Mt48lc4m32b2_16 {}

    impl SdramChip for Mt48lc4m32b2_16 {
        /// Value of the mode register
        const MODE_REGISTER: u16 = BURST_LENGTH_1
            | BURST_TYPE_SEQUENTIAL
            | CAS_LATENCY_3
            | OPERATING_MODE_STANDARD
            | WRITEBURST_MODE_SINGLE;

        /// Timing Parameters
        const TIMING: SdramTiming = SdramTiming {
            startup_delay_ns: 100_000,    // 100 µs
            max_sd_clock_hz: 100_000_000, // 100 MHz
            refresh_period_ns: 15_625,    // 64ms / (4096 rows) = 15625ns
            mode_register_to_active: 2,   // tMRD = 2 cycles
            exit_self_refresh: 7,         // tXSR = 70ns
            active_to_precharge: 4,       // tRAS = 42ns
            row_cycle: 7,                 // tRC = 70ns
            row_precharge: 2,             // tRP = 18ns
            row_to_column: 2,             // tRCD = 18ns
        };

        /// SDRAM controller configuration
        const CONFIG: SdramConfiguration = SdramConfiguration {
            column_bits: 8,
            row_bits: 12,
            memory_data_width: 16, // 32-bit
            internal_banks: 4,     // 4 internal banks
            cas_latency: 3,        // CAS latency = 2
            write_protection: false,
            read_burst: true,
            read_pipe_delay_cycles: 0,
        };
    }
}
