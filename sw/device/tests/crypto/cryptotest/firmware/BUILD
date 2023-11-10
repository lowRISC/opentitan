# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_binary",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
    ],
)

opentitan_binary(
    name = "firmware",
    testonly = True,
    srcs = [":firmware.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_test_rom",
    ],
    deps = [
        ":aes",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
        "//sw/device/tests/crypto/cryptotest/json:commands",
    ],
)
