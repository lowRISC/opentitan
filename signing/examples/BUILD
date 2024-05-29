# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:signing.bzl",
    "offline_fake_ecdsa_sign",
    "offline_presigning_artifacts",
    "offline_signature_attach",
)
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

offline_presigning_artifacts(
    name = "presigning",
    testonly = True,
    srcs = [
        "//sw/device/examples/hello_world",
    ],
    # To sign with real keys, replace the ecdsa_key with the label of a real
    # key.
    # This is left as a fake key so that the presigning artifacts will be
    # appropriate for the `fake_sign` rule below.
    ecdsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "fake_test_key_0",
    },
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    tags = ["manual"],
)

pkg_tar(
    name = "digests",
    testonly = True,
    srcs = [":presigning"],
    mode = "0644",
    tags = ["manual"],
)

# The `fake_sign` rule uses opentitantool to generate the detached signatures
# that would normally be created by the offline signing operation.
# These signatures can be copied into the `signatures` directory and attached
# to the binaries to test the offline signing flow without an HSM operation.
offline_fake_ecdsa_sign(
    name = "fake",
    testonly = True,
    srcs = [":presigning"],
    ecdsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "fake_test_key_0",
    },
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    testonly = True,
    srcs = [
        ":presigning",
    ],
    ecdsa_signatures = [
        "//signing/examples/signatures:ecdsa_signatures",
    ],
    tags = ["manual"],
)
