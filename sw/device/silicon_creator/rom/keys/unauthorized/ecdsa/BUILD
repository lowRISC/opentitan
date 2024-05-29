# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")

package(default_visibility = ["//visibility:public"])

key_ecdsa(
    name = "unauthorized_key_0_ecdsa_p256",
    config = "EcdsaP256",
    method = "local",
    private_key = "unauthorized_key_0_ecdsa_p256.der",
    pub_key = "unauthorized_key_0_ecdsa_p256.pub.der",
    type = "TestKey",
)
