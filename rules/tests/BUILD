# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/tests:const_unittest.bzl", "const_test_suite")
load("//rules/tests:otp_unittest.bzl", "otp_test_suite")
load(
    "//rules:signing.bzl",
    "ownership_signature_test",
    "signature_test",
)

const_test_suite()

otp_test_suite()

signature_test(
    name = "corrupt_signature_test",
    srcs = [
        "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a_corrupted_fpga_cw310_rom_with_fake_keys.prod_key_0.signed.bin",
    ],
    negative_test = True,
)

signature_test(
    name = "wrong_ecdsa_key_test",
    srcs = ["//sw/device/silicon_creator/rom_ext:signed_spx_binaries"],
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset": "dev_key_0"},
    negative_test = True,
)

signature_test(
    name = "wrong_spx_key_test",
    srcs = ["//sw/device/silicon_creator/rom_ext:signed_spx_binaries"],
    negative_test = True,
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:spx_keyset": "dev_key_0"},
)

signature_test(
    name = "wrong_domain_signature_test",
    srcs = [
        "//sw/device/silicon_creator/rom_ext:signed_spx_binaries",
    ],
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset": "prod_key_0"},
    negative_test = True,
    spx_domain = "PrehashedSha256",  # "Pure", "PrehashedSha256"
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:spx_keyset": "prod_key_0"},
)

ownership_signature_test(
    name = "valid_owner_signature_test",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_bin"],
    ecdsa_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
    ecdsa_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_ecdsa_signature",
    spx_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
    spx_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_spx_signature",
)

ownership_signature_test(
    name = "wrong_owner_ecdsa_key_test",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_bin"],
    ecdsa_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key_pub",
    ecdsa_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_ecdsa_signature",
    negative_test = True,
    spx_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
    spx_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_spx_signature",
)

ownership_signature_test(
    name = "wrong_owner_spx_key_test",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_bin"],
    ecdsa_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
    ecdsa_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_ecdsa_signature",
    negative_test = True,
    spx_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key_spx_pub",
    spx_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_spx_signature",
)

genrule(
    name = "corrupt_hybrid_owner_ecdsa_signature",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_ecdsa_signature"],
    outs = ["hybrid_owner.ecdsa_signature.corrupted.bin"],
    cmd = "cp $(location //sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_ecdsa_signature) $(location hybrid_owner.ecdsa_signature.corrupted.bin) && " +
          "sed -i '1s/^./\\x00/' $(location hybrid_owner.ecdsa_signature.corrupted.bin)",
)

ownership_signature_test(
    name = "wrong_owner_ecdsa_signature_test",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_bin"],
    ecdsa_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
    ecdsa_signature = ":corrupt_hybrid_owner_ecdsa_signature",
    negative_test = True,
    spx_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
    spx_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_spx_signature",
)

genrule(
    name = "corrupt_hybrid_owner_spx_signature",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_spx_signature"],
    outs = ["hybrid_owner.spx_signature.corrupted.bin"],
    cmd = "cp $(location //sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_spx_signature) $(location hybrid_owner.spx_signature.corrupted.bin) && " +
          "sed -i '1s/^./\\x00/' $(location hybrid_owner.spx_signature.corrupted.bin)",
)

ownership_signature_test(
    name = "wrong_owner_spx_signature_test",
    srcs = ["//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_bin"],
    ecdsa_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
    ecdsa_signature = "//sw/device/silicon_creator/lib/ownership/testdata:hybrid_owner_ecdsa_signature",
    negative_test = True,
    spx_key = "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
    spx_signature = ":corrupt_hybrid_owner_spx_signature",
)
