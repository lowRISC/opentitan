# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

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
        ":sca",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

cc_library(
    name = "sca",
    srcs = ["sca.c"],
    hdrs = ["sca.h"],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)
