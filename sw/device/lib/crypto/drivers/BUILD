# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest")

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
    ],
)

opentitan_functest(
    name = "aes_test",
    srcs = ["aes_test.c"],
    cw310 = cw310_params(
        tags = ["broken"],
    ),
    deps = [
        ":aes",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
    ],
)

cc_library(
    name = "otbn",
    srcs = ["otbn.c"],
    hdrs = ["otbn.h"],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
    ],
)
