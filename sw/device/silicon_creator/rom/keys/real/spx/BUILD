# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_sphincs_plus")
load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "test_key_0_spx",
    srcs = ["test_key_0_spx.pub.pem"],
)

key_sphincs_plus(
    name = "test_key_0_spx_key",
    config = {"domain": "Pure"},
    method = "hsmtool",
    pub_key = "test_key_0_spx.pub.pem",
    type = "TestKey",
)

filegroup(
    name = "dev_key_0_spx",
    srcs = ["dev_key_0_spx.pub.pem"],
)

key_sphincs_plus(
    name = "dev_key_0_spx_key",
    config = {"domain": "Pure"},
    method = "hsmtool",
    pub_key = "dev_key_0_spx.pub.pem",
    type = "TestKey",
)

filegroup(
    name = "prod_key_0_spx",
    srcs = ["prod_key_0_spx.pub.pem"],
)

key_sphincs_plus(
    name = "prod_key_0_spx_key",
    config = {"domain": "Pure"},
    method = "hsmtool",
    pub_key = "prod_key_0_spx.pub.pem",
    type = "TestKey",
)

filegroup(
    name = "prod_key_1_spx",
    srcs = ["prod_key_1_spx.pub.pem"],
)

key_sphincs_plus(
    name = "prod_key_1_spx_key",
    config = {"domain": "Pure"},
    method = "hsmtool",
    pub_key = "prod_key_1_spx.pub.pem",
    type = "TestKey",
)

keyset(
    name = "spx_keyset",
    keys = {
        "dev_key_0_spx.pub.pem": "dev_key_0",
        "prod_key_0_spx.pub.pem": "prod_spx_0",
        "prod_key_1_spx.pub.pem": "prod_spx_1",
        "test_key_0_spx.pub.pem": "test__0",
    },
    default = "dev__0",
)