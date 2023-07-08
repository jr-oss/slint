/* Copyright © 2021 rp-rs organization
 SPDX-License-Identifier: MIT OR Apache-2.0 */

MEMORY
{
  FLASH    : ORIGIN = 0x08000000, LENGTH = 2M

  /* AXISRAM */
  AXISRAM : ORIGIN = 0x24000000, LENGTH = 512K

  /* SRAM */
  RAM : ORIGIN = 0x30000000, LENGTH = 256K
  /*SRAM1 : ORIGIN = 0x30000000, LENGTH = 128K*/
  /*SRAM2 : ORIGIN = 0x30020000, LENGTH = 128K*/
  SRAM3 : ORIGIN = 0x30040000, LENGTH = 32K
  SRAM4 : ORIGIN = 0x38000000, LENGTH = 64K

  SDRAM    : ORIGIN = 0xD0000000, LENGTH = 8192K
  /*OSPI_ROM : ORIGIN = 0x90000000, LENGTH = 65536K*/
}

_stack_start = ORIGIN(SRAM4) + LENGTH(SRAM4);

SECTIONS {
     .frame_buffer (NOLOAD) : {
       . = ALIGN(4);
       *(.frame_buffer);
       . = ALIGN(4);
     } > SDRAM
}
