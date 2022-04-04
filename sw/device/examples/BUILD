# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "demos",
    srcs = ["demos.c"],
    hdrs = ["demos.h"],
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework",
    ],
)
