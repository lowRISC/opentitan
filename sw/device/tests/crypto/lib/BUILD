# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "crypto_test_lib",
    srcs = ["crypto_test_lib.c"],
    hdrs = ["crypto_test_lib.h"],
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/testing:rand_testutils",
    ],
)
