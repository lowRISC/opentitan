# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "otbn_util",
    srcs = ["otbn_util.c"],
    hdrs = ["otbn_util.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/drivers:otbn",
    ],
)

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["//sw/device/lib/crypto/include:aes.h"],
    deps = [
        ":integrity_check",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:aes",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "integrity_check",
    srcs = ["integrity_check.c"],
    hdrs = ["integrity_check.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)
