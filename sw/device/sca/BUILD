# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_flash_binary")

package(default_visibility = ["//visibility:public"])

opentitan_flash_binary(
    name = "aes_serial",
    srcs = ["aes_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_start_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_flash_binary(
    name = "sha3_serial",
    srcs = ["sha3_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_start_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
    ],
)
