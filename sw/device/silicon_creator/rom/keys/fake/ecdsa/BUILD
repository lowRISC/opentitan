# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")

package(default_visibility = ["//visibility:public"])

key_ecdsa(
    name = "test_key_0_ecdsa_p256",
    pub_key = "test_key_0_ecdsa_p256.pub.der",
    private_key = "test_key_0_ecdsa_p256.der",
    type = "TestKey",
    method = "local",
    config = "EcdsaP256",
)

key_ecdsa(
    name = "dev_key_0_ecdsa_p256",
    pub_key = "test_key_1_ecdsa_p256.pub.der",
    private_key = "test_key_1_ecdsa_p256.der",
    type = "DevKey",
    method = "local",
    config = "EcdsaP256",
)

key_ecdsa(
    name = "prod_key_0_ecdsa_p256",
    pub_key = "prod_key_0_ecdsa_p256.pub.der",
    private_key = "prod_key_0_ecdsa_p256.der",
    type = "ProdKey",
    method = "local",
    config = "EcdsaP256",
)

key_ecdsa(
    name = "prod_key_1_ecdsa_p256",
    pub_key = "prod_key_1_ecdsa_p256.pub.der",
    private_key = "prod_key_1_ecdsa_p256.der",
    type = "ProdKey",
    method = "local",
    config = "EcdsaP256",
)
