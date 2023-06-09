# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

offline_presigning_artifacts(
    name = "presigning_empty_test",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test_slot_a_bin"],
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    rsa_key = "//sw/device/silicon_creator/rom/keys/real/rsa:earlgrey_a0_test_0",
    spx_key = "//sw/device/silicon_creator/rom/keys/real/spx:test_key_0_spx",
    tags = ["manual"],
)

offline_presigning_artifacts(
    name = "presigning_self_hash",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e:rom_e2e_self_hash_bin"],
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    rsa_key = "//sw/device/silicon_creator/rom/keys/real/rsa:earlgrey_a0_test_0",
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
    rsa_signatures = [
        "//signing/rom_tests/signatures:rsa_signatures",
    ],
    tags = ["manual"],
)
