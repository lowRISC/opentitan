# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "address",
    srcs = ["address.c"],
    hdrs = ["address.h"],
    deps = [
        ":params",
        "//sw/device/lib/base:memory",
    ],
)

cc_test(
    name = "address_unittest",
    srcs = ["address_unittest.cc"],
    deps = [
        ":address",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "context",
    hdrs = ["context.h"],
)

cc_library(
    name = "params",
    hdrs = ["params.h"],
)

cc_library(
    name = "thash",
    srcs = ["thash_shake_simple.c"],
    hdrs = ["thash.h"],
    deps = [
        ":address",
        ":context",
        ":params",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/drivers:kmac",
    ],
)
