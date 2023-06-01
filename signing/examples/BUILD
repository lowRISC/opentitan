# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "offline_fake_sign", "offline_presigning_artifacts", "offline_signature_attach")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

offline_presigning_artifacts(
    name = "presigning",
    srcs = [
        "//sw/device/examples/hello_world:hello_world_bin",
    ],
    key_file = "//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
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
offline_fake_sign(
    name = "fake",
    srcs = [":presigning"],
    key_file = "//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0",
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    srcs = [
        ":presigning",
    ],
    signatures = [
        "//signing/examples/signatures:signatures",
    ],
    tags = ["manual"],
)
