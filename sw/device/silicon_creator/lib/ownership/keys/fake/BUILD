# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")
load("//rules/opentitan:keyutils.bzl", "key_ecdsa", "key_sphincs_plus")

package(default_visibility = ["//visibility:public"])

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
    name = "activate_key_spx",
    srcs = ["activate_spx.pem"],
)

filegroup(
    name = "unlock_key_spx",
    srcs = ["unlock_spx.pem"],
)

filegroup(
    name = "app_ecdsa_prod",
    srcs = ["app_prod_ecdsa_p256.der"],
)

filegroup(
    name = "app_prod_ecdsa_pub",
    srcs = ["app_prod_ecdsa_p256.pub.der"],
)

filegroup(
    name = "app_dev",
    srcs = ["app_dev_ecdsa_p256.der"],
)

filegroup(
    name = "app_dev_pub",
    srcs = ["app_dev_ecdsa_p256.pub.der"],
)

filegroup(
    name = "app_spx_prod",
    srcs = ["app_prod_spx.pem"],
)

filegroup(
    name = "app_spx_prod_pub",
    srcs = ["app_prod_spx.pub.pem"],
)
keyset(
    name = "ecdsa_keys",
    build_setting_default = "",
    keys = {
        "owner_ecdsa_p256.pub.der": "owner_ecdsa_p256",
        "owner_ecdsa_p256.der": "owner_ecdsa_p256",
        "activate_ecdsa_p256.der": "activate_ecdsa_p256",
        "activate_ecdsa_p256.pub.der": "activate_ecdsa_p256",
        "unlock_ecdsa_p256.pub.der": "unlock_ecdsa_p256",
        "unlock_ecdsa_p256.der": "unlock_ecdsa_p256",
        "app_prod_ecdsa_p256.pub.der": "app_prod_ecdsa_p256",
        "app_prod_ecdsa_p256.der": "app_prod_ecdsa_p256",
        "app_dev_ecdsa_p256.pub.der": "app_dev_ecdsa_p256",
        "app_dev_ecdsa_p256.der": "app_dev_ecdsa_p256",
        "app_test_ecdsa_p256.pub.der": "app_test_ecdsa_p256",
        "app_test_ecdsa_p256.der": "app_test_ecdsa_p256",
        "app_unauthorized_ecdsa_p256.pub.der": "app_unauthorized_ecdsa_p256",
        "app_unauthorized_ecdsa_p256.der": "app_unauthorized_ecdsa_p256",
    },
    profile = "sival_root",
    tool = "//signing:token",
)

keyset(
    name = "spx_keys",
    build_setting_default = "",
    keys = {
        "owner_spx.pem": "owner_spx",
        "owner_spx.pub.pem": "owner_spx",
        "activate_spx.pub.pem": "activate_spx",
        "activate_spx.pem": "activate_spx",
        "unlock_spx.pub.pem": "unlock_spx",
        "unlock_spx.pem": "unlock_spx",
        "app_prod_spx.pem": "app_prod_spx",
        "app_prod_spx.pub.pem": "app_prod_spx",
        "app_dev_spx.pem": "app_dev_spx",
        "app_dev_spx.pub.pem": "app_dev_spx",
        "app_test_spx.pem": "app_test_spx",
        "app_test_spx.pub.pem": "app_test_spx",
        "app_unauthorized_spx.pem": "app_unauthorized_spx",
        "app_unauthorized_spx.pub.pem": "app_unauthorized_spx",
    },
    profile = "sival_root",
    tool = "//signing:token",
)

pkg_files(
    name = "fpga_dev_files",
    testonly = True,
    srcs = [
        ":app_dev",
        ":app_dev_pub",
        ":app_ecdsa_prod",
        ":app_prod_ecdsa_pub",
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
