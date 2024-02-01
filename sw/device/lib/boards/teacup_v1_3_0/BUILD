# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "leds",
    srcs = ["leds.c"],
    hdrs = ["leds.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:i2c_testutils",
    ],
)
