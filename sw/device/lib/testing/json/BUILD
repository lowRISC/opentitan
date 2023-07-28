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
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/top_earlgrey/sw/dif:gpio",
    ],
)

cc_library(
    name = "i2c_target",
    srcs = ["i2c_target.c"],
    hdrs = ["i2c_target.h"],
    deps = ["//sw/device/lib/ujson"],
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
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:status",
        "//sw/lib/sw/device/runtime:print",
        "//sw/top_earlgrey/sw/dif:pinmux",
    ],
)

cc_library(
    name = "spi_passthru",
    srcs = ["spi_passthru.c"],
    hdrs = ["spi_passthru.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "provisioning_data",
    srcs = ["provisioning_data.c"],
    hdrs = ["provisioning_data.h"],
    deps = ["//sw/device/lib/ujson"],
)
