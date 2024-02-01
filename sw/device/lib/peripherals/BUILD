# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "ssd1131_screen",
    srcs = ["ssd1131_screen.c"],
    hdrs = ["ssd1131_screen.h"],
    deps = [
        "//sw/device/examples/teacup_demos/data:bitmaps",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:log",
    ],
)
