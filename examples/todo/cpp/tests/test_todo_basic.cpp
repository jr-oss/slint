// Copyright © SixtyFPS GmbH <info@slint.dev>
// SPDX-License-Identifier: MIT

#include <slint-testing.h>
#include "../app.h"

#define CATCH_CONFIG_MAIN
#include "catch2/catch.hpp"

SCENARIO("Basic TEST")
{
    slint::testing::init();
    auto state = create_ui();
    using todo_ui::TodoItem;
    state.todo_model->set_vector({ TodoItem { "first", true } });

    auto results = slint::testing::ElementHandle::find_by_accessible_label(
            state.mainWindow, "What needs to be done?");

    REQUIRE(results.size() == 1);
    auto line_edit = results[0];
    line_edit.set_accessible_value("second");

    results = slint::testing::ElementHandle::find_by_accessible_label(state.mainWindow,
                                                                      "Add New Entry");
    REQUIRE(results.size() == 1);
    auto button = results[0];
    button.invoke_accessible_default_action();

    REQUIRE(state.todo_model->row_count() == 2);
    REQUIRE(state.todo_model->row_data(0).value() == TodoItem { "first", true });
    REQUIRE(state.todo_model->row_data(1).value() == TodoItem { "second", false });

    REQUIRE(line_edit.accessible_value() == "");
}
