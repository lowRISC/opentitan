# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")
load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

key_ecdsa(
    name = "unauthorized_key_0_ecdsa_p256",
    method = "local",
    private_key = "unauthorized_key_0_ecdsa_p256.der",
    pub_key = "unauthorized_key_0_ecdsa_p256.pub.der",
    type = "TestKey",
)

keyset(
    name = "ecdsa_keyset",
    build_setting_default = "",
    keys = {
        "unauthorized_key_0_ecdsa_p256.der": "unauthorized_key_0",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)
