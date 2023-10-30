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
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:print",
    ],
)

cc_library(
    name = "sca",
    srcs = ["sca.c"],
    hdrs = ["sca.h"],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
    ],
)
