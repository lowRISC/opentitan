# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_sphincs_plus")

package(default_visibility = ["//visibility:public"])

key_sphincs_plus(
    name = "test_key_0_spx_key_info",
    pub_key = "test_key_0_spx.pub.pem",
    private_key = "test_key_0_spx.pem",
    config = "Shake128s",
    type = "TestKey",
    method = "local",
)

filegroup(
    name = "test_key_0_spx",
    srcs = ["test_key_0_spx.pem"],
)

key_sphincs_plus(
    name = "dev_key_0_spx_key_info",
    pub_key = "dev_key_0_spx.pub.pem",
    private_key = "dev_key_0_spx.pem",
    config = "Shake128s",
    type = "DevKey",
    method = "local",
)

filegroup(
    name = "dev_key_0_spx",
    srcs = ["dev_key_0_spx.pem"],
)

key_sphincs_plus(
    name = "prod_key_0_spx_key_info",
    pub_key = "prod_key_0_spx.pub.pem",
    private_key = "prod_key_0_spx.pem",
    config = "Shake128s",
    type = "ProdKey",
    method = "local",
)

filegroup(
    name = "prod_key_0_spx",
    srcs = ["prod_key_0_spx.pem"],
)

key_sphincs_plus(
    name = "prod_key_1_spx_key_info",
    pub_key = "prod_key_1_spx.pub.pem",
    private_key = "prod_key_1_spx.pem",
    config = "Shake128s",
    type = "ProdKey",
    method = "local",
)

filegroup(
    name = "prod_key_1_spx",
    srcs = ["prod_key_1_spx.pem"],
)
