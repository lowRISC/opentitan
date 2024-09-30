# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//sw/device/lib/base:memory",
    ],
)

cc_library(
    name = "prng",
    srcs = ["prng.c"],
    hdrs = ["prng.h"],
)

cc_test(
    name = "prng_unittest",
    srcs = ["prng_unittest.cc"],
    deps = [
        ":prng",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "simple_serial",
    srcs = ["simple_serial.c"],
    hdrs = ["simple_serial.h"],
    deps = [
        ":prng",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:print",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
    ],
)
