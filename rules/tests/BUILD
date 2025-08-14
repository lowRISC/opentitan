# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/tests:const_unittest.bzl", "const_test_suite")
load("//rules/tests:otp_unittest.bzl", "otp_test_suite")
load("//rules:signing.bzl", "signature_test")

const_test_suite()

otp_test_suite()

signature_test(
    name = "corrupt_signature_test",
    srcs = [
        "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a_corrupted_fpga_cw310_rom_with_fake_keys.fake_ecdsa_prod_key_0.signed.bin",
    ],
    negative_test = True,
)

signature_test(
    name = "wrong_ecdsa_key_test",
    srcs = ["//sw/device/silicon_creator/rom_ext:signed_spx_binaries"],
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:dev_key_0_ecdsa_p256": "dev_key_0"},
    negative_test = True,
)

signature_test(
    name = "wrong_spx_key_test",
    srcs = ["//sw/device/silicon_creator/rom_ext:signed_spx_binaries"],
    negative_test = True,
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:dev_key_0_spx": "dev_key_0"},
)

signature_test(
    name = "wrong_domain_signature_test",
    srcs = [
        "//sw/device/silicon_creator/rom_ext:signed_spx_binaries",
    ],
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    negative_test = True,
    spx_domain = "PrehashedSha256",  # "Pure", "PrehashedSha256"
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx_key": "prod_spx_0"},
)
