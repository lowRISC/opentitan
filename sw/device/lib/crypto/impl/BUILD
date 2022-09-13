# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "otbn_util",
    srcs = ["otbn_util.c"],
    hdrs = ["otbn_util.h"],
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
    ],
)

cc_library(
    name = "integrity_check",
    srcs = ["integrity_check.c"],
    hdrs = [
        "integrity_check.h",
        "//sw/device/lib/crypto/include:datatypes.h",
    ],
    deps = [
        "//sw/device/lib/base:hardened",
    ],
)
