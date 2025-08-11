# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")

package(default_visibility = ["//visibility:public"])

keyset(
    name = "unauthorized_keys",
    build_setting_default = "",
    keys = {
        "unauthorized_key_0_ecdsa_p256.pub.der": "unauthorized_key_0_ecdsa_p256",
        "unauthorized_key_0_ecdsa_p256.der": "unauthorized_key_0_ecdsa_p256",
    },
    profile = "unauthorized_root",
    tool = "//signing:token",
)