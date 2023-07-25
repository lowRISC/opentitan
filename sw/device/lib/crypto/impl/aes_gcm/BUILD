# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes_gcm",
    srcs = ["aes_gcm.c"],
    hdrs = ["aes_gcm.h"],
    deps = [
        ":ghash",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:aes",
    ],
)

cc_library(
    name = "ghash",
    srcs = ["ghash.c"],
    hdrs = ["ghash.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
    ],
)

cc_test(
    name = "ghash_unittest",
    srcs = ["ghash_unittest.cc"],
    deps = [
        ":ghash",
        "@googletest//:gtest_main",
    ],
)
