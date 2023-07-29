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
        "//sw/device/lib/crypto/drivers:aes",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:hardened_memory",
        "//sw/lib/sw/device/base:memory",
    ],
)

cc_library(
    name = "ghash",
    srcs = ["ghash.c"],
    hdrs = ["ghash.h"],
    deps = [
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
    ],
)
