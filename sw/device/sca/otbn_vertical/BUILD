# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "opentitan_binary")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "ecc256_keygen_serial",
    srcs = ["ecc256_keygen_serial.c"],
    hdrs = ["ecc256_keygen_serial.h"],
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
        "//sw/otbn/crypto:p256_key_from_seed_sca",
    ],
)

cc_library(
    name = "ecc256_modinv_serial",
    srcs = ["ecc256_modinv_serial.c"],
    hdrs = ["ecc256_modinv_serial.h"],
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
        "//sw/otbn/crypto:p256_mod_inv_sca",
    ],
)

opentitan_binary(
    name = "otbn_vertical_serial",
    testonly = True,
    srcs = ["otbn_vertical_serial.c"],
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
        "//sw/device/sca/otbn_vertical:ecc256_keygen_serial",
        "//sw/device/sca/otbn_vertical:ecc256_modinv_serial",
        "//sw/otbn/crypto:p256_mod_inv_sca",
    ],
)
