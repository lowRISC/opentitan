# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

offline_presigning_artifacts(
    name = "presigning_empty_test",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e/sigverify_spx:empty_test_sigverify_spx"],
    ecdsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0_ecdsa_p256",
    },
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    spx_key = {
        "//sw/device/silicon_creator/rom/keys/real/spx:test_key_0_spx": "earlgrey_a0_test_0_spx",
    },
    tags = ["manual"],
)

offline_presigning_artifacts(
    name = "presigning_self_hash",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e/release:rom_e2e_self_hash_bin"],
    ecdsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0_ecdsa_p256",
    },
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    tags = ["manual"],
)

pkg_tar(
    name = "digests",
    testonly = True,
    srcs = [
        ":presigning_empty_test",
        ":presigning_self_hash",
    ],
    mode = "0644",
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    testonly = True,
    srcs = [
        ":presigning_empty_test",
        ":presigning_self_hash",
    ],
    ecdsa_signatures = [
        "//signing/rom_tests/signatures:ecdsa_signatures",
    ],
    spx_signatures = [
        "//signing/rom_tests/signatures:spx_signatures",
    ],
    tags = ["manual"],
)
