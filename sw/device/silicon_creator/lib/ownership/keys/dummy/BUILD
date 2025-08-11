# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:keyutils.bzl", "key_ecdsa")
load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

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
    name = "app_prod_ecdsa_pub",
    srcs = ["app_prod_ecdsa_p256.pub.der"],
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

    },
    profile = "sival_root",
    tool = "//signing:token",
)

key_ecdsa(
    name = "app_prod_ecdsa",
    method = "local",
    private_key = "app_prod_ecdsa_p256.der",
    pub_key = "app_prod_ecdsa_p256.pub.der",
    type = "ProdKey",
)
