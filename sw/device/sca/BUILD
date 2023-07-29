# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_flash_binary")

package(default_visibility = ["//visibility:public"])

alias(
    name = "aes_serial_aes_testutils",
    actual = select({
        "//sw/device:is_english_breakfast": "//sw/device:nothing",
        "//conditions:default": "//sw/device/lib/testing:aes_testutils",
    }),
    visibility = ["//visibility:private"],
)

opentitan_flash_binary(
    name = "aes_serial",
    srcs = ["aes_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/device/runtime:print",
        "//sw/top_earlgrey/sw/dif:aes",
    ],
)

opentitan_flash_binary(
    name = "kmac_serial",
    srcs = ["kmac_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/device/runtime:print",
        "//sw/top_earlgrey/sw/dif:kmac",
    ],
)

opentitan_flash_binary(
    name = "sha3_serial",
    srcs = ["sha3_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/device/runtime:print",
        "//sw/top_earlgrey/sw/dif:kmac",
    ],
)

opentitan_flash_binary(
    name = "ecc384_serial",
    srcs = ["ecc384_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/crypto:p384_ecdsa_sca",
        "//sw/top_earlgrey/sw/device/runtime:print",
    ],
)

opentitan_flash_binary(
    name = "ecc256_sign_serial",
    srcs = ["ecc256_sign_serial.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/crypto:p256_ecdsa_sca",
        "//sw/top_earlgrey/sw/device/runtime:print",
    ],
)
