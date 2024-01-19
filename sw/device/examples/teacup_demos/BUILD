# Copyright lowRISC contributors.
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
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
