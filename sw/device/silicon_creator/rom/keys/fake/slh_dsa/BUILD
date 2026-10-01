# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

keyset(
    name = "slh_dsa_keyset",
    build_setting_default = "",
    keys = {
        "test_key_0_slh_dsa.pem": "test_key_0",
        "dev_key_0_slh_dsa.pem": "dev_key_0",
        "prod_key_0_slh_dsa.pem": "prod_key_0",
        "prod_key_1_slh_dsa.pem": "prod_key_1:domain=PreHashedSha256",
    },
    keytype = "slh-dsa",
    profile = "local",
    tool = "//signing/tokens:local",
)
