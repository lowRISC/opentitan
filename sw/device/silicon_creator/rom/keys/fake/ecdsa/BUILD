# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

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
