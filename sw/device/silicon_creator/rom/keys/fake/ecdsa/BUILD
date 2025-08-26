# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")
load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

key_ecdsa(
    name = "test_key_0_ecdsa_p256",
    method = "local",
    private_key = "test_key_0_ecdsa_p256.der",
    pub_key = "test_key_0_ecdsa_p256.pub.der",
    type = "TestKey",
)

key_ecdsa(
    name = "dev_key_0_ecdsa_p256",
    method = "local",
    private_key = "dev_key_0_ecdsa_p256.der",
    pub_key = "dev_key_0_ecdsa_p256.pub.der",
    type = "DevKey",
)

key_ecdsa(
    name = "prod_key_0_ecdsa_p256",
    method = "local",
    private_key = "prod_key_0_ecdsa_p256.der",
    pub_key = "prod_key_0_ecdsa_p256.pub.der",
    type = "ProdKey",
)

key_ecdsa(
    name = "prod_key_1_ecdsa_p256",
    method = "local",
    private_key = "prod_key_1_ecdsa_p256.der",
    pub_key = "prod_key_1_ecdsa_p256.pub.der",
    type = "ProdKey",
)

keyset(
    name = "ecdsa_keyset",
    build_setting_default = "",
    keys = {
        "test_key_0_ecdsa_p256.der": "test_key_0",
        "dev_key_0_ecdsa_p256.der": "dev_key_0",
        "prod_key_0_ecdsa_p256.der": "prod_key_0",
        "prod_key_1_ecdsa_p256.der": "prod_key_1",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)
