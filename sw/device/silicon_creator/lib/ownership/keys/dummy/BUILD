# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")

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
    name = "app_prod_ecdsa_pub",
    srcs = ["app_prod_ecdsa_p256.pub.der"],
)

key_ecdsa(
    name = "app_prod_ecdsa",
    config = "EcdsaP256",
    method = "local",
    private_key = "app_prod_ecdsa_p256.der",
    pub_key = "app_prod_ecdsa_p256.pub.der",
    type = "ProdKey",
)
