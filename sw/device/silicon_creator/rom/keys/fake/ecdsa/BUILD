# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")

package(default_visibility = ["//visibility:public"])

keyset(
    name = "ecdsa_keys",
    build_setting_default = "",
    keys = {
        "test_key_0_ecdsa_p256.pub.der": "test_key_0_ecdsa_p256",
        "test_key_0_ecdsa_p256.der": "test_key_0_ecdsa_p256",
        "dev_key_0_ecdsa_p256.pub.der": "dev_key_0_ecdsa_p256",
        "dev_key_0_ecdsa_p256.der": "dev_key_0_ecdsa_p256",
        "prod_key_0_ecdsa_p256.pub.der": "prod_key_0_ecdsa_p256",
        "prod_key_0_ecdsa_p256.der": "prod_key_0_ecdsa_p256",   
        "prod_key_1_ecdsa_p256.pub.der": "prod_key_1_ecdsa_p256",
        "prod_key_1_ecdsa_p256.der": "prod_key_1_ecdsa_p256",
    },
    profile = "sival_root",
    tool = "//signing:token",
)
