# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "opentitan_binary")

package(default_visibility = ["//visibility:public"])

alias(
    name = "aes_serial_aes_testutils",
    actual = select({
        "//sw/device:is_english_breakfast": "//sw/device:nothing",
        "//conditions:default": "//sw/device/lib/testing:aes_testutils",
    }),
    visibility = ["//visibility:private"],
)

opentitan_binary(
    name = "aes_serial",
    testonly = True,
    srcs = ["aes_serial.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw310",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:aes",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_binary(
    name = "kmac_serial",
    testonly = True,
    srcs = ["kmac_serial.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw310",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_binary(
    name = "sha3_serial",
    testonly = True,
    srcs = ["sha3_serial.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw310",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_binary(
    name = "ecc384_serial",
    testonly = True,
    srcs = ["ecc384_serial.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw310",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/otbn/crypto:p384_ecdsa_sca",
    ],
)

opentitan_binary(
    name = "ecc256_sign_serial",
    testonly = True,
    srcs = ["ecc256_sign_serial.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw310",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/sca/lib:simple_serial",
        "//sw/otbn/crypto:p256_ecdsa_sca",
    ],
)
