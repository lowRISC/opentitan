# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "target",
    srcs = ["target.c"],
    hdrs = ["target.h"],
)

cc_test(
    name = "host_unittest",
    srcs = ["host_unittest.cc"],
    deps = [
        ":target",
        "@googletest//:gtest_main",
    ],
)
