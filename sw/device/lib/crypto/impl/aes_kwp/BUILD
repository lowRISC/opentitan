# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes_kwp",
    srcs = ["aes_kwp.c"],
    hdrs = ["aes_kwp.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:aes",
    ],
)
