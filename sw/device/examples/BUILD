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
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:gpio",
        "//sw/top_earlgrey/sw/dif:spi_device",
        "//sw/top_earlgrey/sw/dif:uart",
    ],
)
