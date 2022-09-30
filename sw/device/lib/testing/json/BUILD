# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "command",
    srcs = ["command.c"],
    hdrs = ["command.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "chip_specific_startup",
    srcs = ["chip_specific_startup.c"],
    hdrs = ["chip_specific_startup.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "gpio",
    srcs = ["gpio.c"],
    hdrs = ["gpio.h"],
    deps = [
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
    ],
)

cc_library(
    name = "pinmux",
    srcs = ["pinmux.c"],
    hdrs = ["pinmux.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/ujson",
    ],
)

cc_library(
    name = "pinmux_config",
    srcs = ["pinmux_config.c"],
    hdrs = ["pinmux_config.h"],
    deps = [
        ":pinmux",
        "//sw/device/lib/ujson",
    ],
)
