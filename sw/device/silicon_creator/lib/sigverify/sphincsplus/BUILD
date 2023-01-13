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
    name = "fors",
    srcs = ["fors.c"],
    hdrs = ["fors.h"],
    deps = [
        ":address",
        ":hash",
        ":thash",
        ":utils",
    ],
)

cc_library(
    name = "hash",
    srcs = ["hash_shake.c"],
    hdrs = ["hash.h"],
    deps = [
        ":address",
        ":context",
        ":params",
        ":utils",
        "//sw/device/silicon_creator/lib/drivers:kmac",
    ],
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

cc_library(
    name = "utils",
    srcs = ["utils.c"],
    hdrs = ["utils.h"],
    deps = [
        ":address",
        ":params",
        ":thash",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_library(
    name = "verify",
    srcs = ["verify.c"],
    hdrs = ["verify.h"],
    deps = [
        ":address",
        ":context",
        ":fors",
        ":hash",
        ":params",
        ":thash",
        ":utils",
        ":wots",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_library(
    name = "wots",
    srcs = ["wots.c"],
    hdrs = ["wots.h"],
    deps = [
        ":address",
        ":hash",
        ":params",
        ":thash",
        ":utils",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:kmac",
    ],
)
