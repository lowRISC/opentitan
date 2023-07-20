# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "dif_base",
    srcs = ["dif_base.c"],
    hdrs = ["dif_base.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/internal:status",
    ],
)

cc_library(
    name = "dif_test_base",
    testonly = True,
    hdrs = ["dif_test_base.h"],
    deps = [
        ":dif_base",
        "@googletest//:gtest",
    ],
)
