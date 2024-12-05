# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "teacup_leds_demo",
    srcs = ["teacup_leds_demo.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/boards/teacup_v1_3_0:leds",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "teacup_leds_and_screen_demo",
    srcs = ["teacup_leds_and_screen_demo.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/examples/teacup_demos/data:bitmaps",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/boards/teacup_v1_3_0:leds",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/peripherals:ssd1131_screen",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
