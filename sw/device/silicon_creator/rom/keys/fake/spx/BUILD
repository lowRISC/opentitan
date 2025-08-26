# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_sphincs_plus")
load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "test_key_0_spx",
    srcs = ["test_key_0_spx.pem"],
)

key_sphincs_plus(
    name = "test_key_0_spx_key",
    config = {"domain": "Pure"},
    method = "local",
    private_key = "test_key_0_spx.pem",
    pub_key = "test_key_0_spx.pub.pem",
    type = "TestKey",
)

filegroup(
    name = "dev_key_0_spx",
    srcs = ["dev_key_0_spx.pem"],
)

key_sphincs_plus(
    name = "dev_key_0_spx_key",
    config = {"domain": "Pure"},
    method = "local",
    private_key = "dev_key_0_spx.pem",
    pub_key = "dev_key_0_spx.pub.pem",
    type = "TestKey",
)

filegroup(
    name = "prod_key_0_spx",
    srcs = ["prod_key_0_spx.pem"],
)

key_sphincs_plus(
    name = "prod_key_0_spx_key",
    config = {"domain": "Pure"},
    method = "local",
    private_key = "prod_key_0_spx.pem",
    pub_key = "prod_key_0_spx.pub.pem",
    type = "TestKey",
)

filegroup(
    name = "prod_key_1_spx",
    srcs = ["prod_key_1_spx.pem"],
)

key_sphincs_plus(
    name = "prod_key_1_spx_key",
    config = {
        "domain": "PreHashedSha256",
    },
    method = "local",
    private_key = "prod_key_1_spx.pem",
    pub_key = "prod_key_1_spx.pub.pem",
    type = "TestKey",
)

keyset(
    name = "spx_keyset",
    build_setting_default = "",
    keys = {
        "test_key_0_spx.pem": "test_key_0",
        "dev_key_0_spx.pem": "dev_key_0",
        "prod_key_0_spx.pem": "prod_key_0",
        "prod_key_1_spx.pem": "prod_key_1:domain=PreHashedSha256",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)
