# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "fips_kat_rom_test",
    srcs = ["fips_kat_rom_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        timeout = "moderate",
    ),
    deps = [
        "//hw/top:csrng_c_regs",
        "//hw/top:entropy_src_c_regs",
        "//hw/top/dt",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:aes_gcm",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_curve25519",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:hkdf",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:kdf_ctr",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:kmac",
        "//sw/device/lib/crypto/impl:kmac_kdf",
        "//sw/device/lib/crypto/impl:mldsa",
        "//sw/device/lib/crypto/impl:mlkem",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl:sha3",
        "//sw/device/lib/crypto/impl/aes_kwp",
        "//sw/device/lib/crypto/impl/mldsa",
        "//sw/device/lib/crypto/impl/mlkem",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_src_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_isrs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:epmp_defs",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
        "//sw/device/silicon_creator/rom:fips_kat_table",
    ],
)
