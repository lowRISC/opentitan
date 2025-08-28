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

key_ecdsa(
    name = "app_prod_ecdsa",
    method = "local",
    private_key = "app_prod_ecdsa_p256.der",
    pub_key = "app_prod_ecdsa_p256.pub.der",
    type = "ProdKey",
)

keyset(
    name = "owner_spx_keyset",
    build_setting_default = "",
    keys = {
        "owner_spx.pem": "owner_key_0",
        "owner_spx.pub.pem": "owner_key_0",
        "activate_spx.pem": "activate_key_0",
        "activate_spx.pub.pem": "activate_key_0",
        "unlock_spx.pem": "unlock_key_0",
        "unlock_spx.pub.pem": "unlock_key_0",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)

keyset(
    name = "owner_ecdsa_keyset",
    build_setting_default = "",
    keys = {
        "owner_ecdsa_p256.pub.der": "owner_key_0",
        "owner_ecdsa_p256.der": "owner_key_0",
        "activate_ecdsa_p256.pub.der": "activate_key_0",
        "activate_ecdsa_p256.der": "activate_key_0",
        "unlock_ecdsa_p256.pub.der": "unlock_key_0",
        "unlock_ecdsa_p256.der": "unlock_key_0",
        "app_prod_ecdsa_p256.pub.der": "app_prod",
        "app_prod_ecdsa_p256.der": "app_prod",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)
