# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
    srcs = ["dif_base.c"],
    hdrs = ["dif_base.h"],
    deps = [
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/base/internal:status",
    ],
)

cc_library(
    name = "test_base",
    testonly = True,
    hdrs = ["dif_test_base.h"],
    deps = [
        ":base",
        "@googletest//:gtest",
    ],
)
