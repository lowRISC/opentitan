# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:signing.bzl",
    "offline_fake_rsa_sign",
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
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
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
    testonly = True,
    srcs = [":presigning"],
    mode = "0644",
    tags = ["manual"],
)

offline_presigning_artifacts(
    name = "presigning_ecdsa",
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
    name = "digests_ecdsa",
    testonly = True,
    srcs = [":presigning_ecdsa"],
    mode = "0644",
    tags = ["manual"],
)

# The `fake_sign` rule uses opentitantool to generate the detached signatures
# that would normally be created by the offline signing operation.
# These signatures can be copied into the `signatures` directory and attached
# to the binaries to test the offline signing flow without an HSM operation.
offline_fake_rsa_sign(
    name = "fake",
    testonly = True,
    srcs = [":presigning"],
    rsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "fake_test_key_0",
    },
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    testonly = True,
    srcs = [
        ":presigning",
    ],
    rsa_signatures = [
        "//signing/examples/signatures:rsa_signatures",
    ],
    tags = ["manual"],
)
