# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "demos",
    srcs = ["demos.c"],
    hdrs = ["demos.h"],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)
