# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cc_library(
    name = "asn1",
    srcs = ["asn1.c"],
    hdrs = ["asn1.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
    ],
)

cc_test(
    name = "asn1_unittest",
    srcs = ["asn1_unittest.cc"],
    deps = [
        ":asn1",
        "@googletest//:gtest_main",
    ],
)
