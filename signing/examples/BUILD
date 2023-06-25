# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "offline_fake_rsa_sign", "offline_presigning_artifacts", "offline_signature_attach")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

offline_presigning_artifacts(
    name = "presigning",
    srcs = [
        "//sw/device/examples/hello_world:hello_world_bin",
    ],
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    # To sign with real keys, replace the rsa_key with the label of a real
    # key (e.g. //sw/device/silicon_creator/rom/keys/real/rsa:earlgrey_a0_test_0).
    # This is left as a fake key so that the presigning artifacts will be
    # appropriate for the `fake_sign` rule below.
    rsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "fake_test_key_0",
    },
    tags = ["manual"],
)

pkg_tar(
    name = "digests",
    srcs = [":presigning"],
    mode = "0644",
    tags = ["manual"],
)

# The `fake_sign` rule uses opentitantool to generate the detached signatures
# that would normally be created by the offline signing operation.
# These signatures can be copied into the `signatures` directory and attached
# to the binaries to test the offline signing flow without an HSM operation.
offline_fake_rsa_sign(
    name = "fake",
    srcs = [":presigning"],
    rsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "fake_test_key_0",
    },
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    srcs = [
        ":presigning",
    ],
    rsa_signatures = [
        "//signing/examples/signatures:rsa_signatures",
    ],
    tags = ["manual"],
)
