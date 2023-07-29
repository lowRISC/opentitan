# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "print",
    srcs = ["//sw/lib/sw/device/runtime:print.c"],
    hdrs = ["//sw/lib/sw/device/runtime:print"],
    deps = [
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:status",
        "//sw/lib/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

cc_test(
    name = "print_unittest",
    srcs = ["//sw/lib/sw/device/runtime:print_unittest.cc"],
    deps = [
        ":print",
        "@com_google_absl//absl/strings:str_format",
        "@googletest//:gtest_main",
    ],
)
