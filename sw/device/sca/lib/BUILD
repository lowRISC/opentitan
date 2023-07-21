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
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/common/dif:base",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:print",
        "//sw/top_earlgrey/sw/dif:uart",
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
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/top_earlgrey/sw/dif:clkmgr",
        "//sw/top_earlgrey/sw/dif:csrng",
        "//sw/top_earlgrey/sw/dif:edn",
        "//sw/top_earlgrey/sw/dif:entropy_src",
        "//sw/top_earlgrey/sw/dif:gpio",
        "//sw/top_earlgrey/sw/dif:pinmux",
        "//sw/top_earlgrey/sw/dif:rv_timer",
        "//sw/top_earlgrey/sw/dif:uart",
    ],
)
