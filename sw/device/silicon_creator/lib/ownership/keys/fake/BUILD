# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@opentitan_signing_infra//signing:defs.bzl", "keyset")
load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_keys",
    srcs = glob([
        "*.der",
        "*.pem",
    ]),
)

cc_library(
    name = "includes",
    testonly = True,
    hdrs = [
        "activate_ecdsa_p256.h",
        "activate_spx.h",
        "app_dev_ecdsa_p256.h",
        "app_dev_spx.h",
        "app_prod_ecdsa_p256.h",
        "app_prod_spx.h",
        "app_test_ecdsa_p256.h",
        "owner_ecdsa_p256.h",
        "owner_spx.h",
        "unlock_ecdsa_p256.h",
        "unlock_spx.h",
    ],
)

cc_library(
    name = "fake",
    srcs = [
        "ownership_ecdsa_keys_fake.c",
    ],
    hdrs = [
        "no_owner_recovery_ecdsa_p256.h",
    ],
    deps = [
        "//sw/device/silicon_creator/lib/ownership:ownership_key",
    ],
    alwayslink = True,
)

filegroup(
    name = "no_owner_recovery_key",
    srcs = ["no_owner_recovery_ecdsa_p256.der"],
)

filegroup(
    name = "owner_key",
    srcs = ["owner_ecdsa_p256.der"],
)

filegroup(
    name = "owner_key_pub",
    srcs = ["owner_ecdsa_p256.pub.der"],
)

filegroup(
    name = "activate_key",
    srcs = ["activate_ecdsa_p256.der"],
)

filegroup(
    name = "unlock_key",
    srcs = ["unlock_ecdsa_p256.der"],
)

filegroup(
    name = "owner_key_spx",
    srcs = ["owner_spx.pem"],
)

filegroup(
    name = "owner_key_spx_pub",
    srcs = ["owner_spx.pub.pem"],
)

filegroup(
    name = "owner_key_slh_dsa",
    srcs = ["owner_slh_dsa.pem"],
)

filegroup(
    name = "owner_key_slh_dsa_pub",
    srcs = ["owner_slh_dsa.pub.pem"],
)

filegroup(
    name = "activate_key_spx",
    srcs = ["activate_spx.pem"],
)

filegroup(
    name = "activate_key_slh_dsa",
    srcs = ["activate_slh_dsa.pem"],
)

filegroup(
    name = "unlock_key_spx",
    srcs = ["unlock_spx.pem"],
)

filegroup(
    name = "unlock_key_slh_dsa",
    srcs = ["unlock_slh_dsa.pem"],
)

# The ownership e2e tests need access to both the app_prod_ecdsa and app_dev_pub public key files below.
filegroup(
    name = "app_prod_ecdsa_pub",
    srcs = ["app_prod_ecdsa_p256.pub.der"],
)

filegroup(
    name = "app_dev_pub",
    srcs = ["app_dev_ecdsa_p256.pub.der"],
)

pkg_files(
    name = "fpga_dev_files",
    testonly = True,
    srcs = [
        ":app_dev_pub",
        ":app_prod_ecdsa_pub",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:slh_dsa_keyset",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:spx_keyset",
    ],
)

pkg_filegroup(
    name = "fpga_dev_pkg",
    testonly = True,
    srcs = [
        ":fpga_dev_files",
    ],
    prefix = "fake_keys",
)

keyset(
    name = "ecdsa_keyset",
    build_setting_default = "",
    keys = {
        "app_prod_ecdsa_p256.der": "app_prod_0",
        "app_dev_ecdsa_p256.der": "app_dev_0",
        "app_test_ecdsa_p256.der": "app_test_0",
        "app_unauthorized_ecdsa_p256.der": "app_unauthorized_0",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)

keyset(
    name = "spx_keyset",
    build_setting_default = "",
    keys = {
        "app_prod_spx.pem": "app_prod_0",
        "app_dev_spx.pem": "app_dev_0:domain=PreHashedSha256",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)

keyset(
    name = "slh_dsa_keyset",
    build_setting_default = "",
    keys = {
        "app_prod_slh_dsa.pem": "app_prod_0",
        "app_dev_slh_dsa.pem": "app_dev_0",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)
