# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "signing_tool")

package(default_visibility = ["//visibility:public"])

config_setting(
    name = "earlgrey_a0_test_0",
    define_values = {
        "token": "earlgrey_a0",
        "key": "test_0",
    },
)

config_setting(
    name = "earlgrey_a0_dev_0",
    define_values = {
        "token": "earlgrey_a0",
        "key": "dev_0",
    },
)

signing_tool(
    name = "hsmtool",
    data = [
        "@sc_hsm//:gen_dir",
    ],
    env = {
        "HSMTOOL_MODULE": "$(location @sc_hsm//:gen_dir)/lib/libsc-hsm-pkcs11.so",
    },
    location = "offline",
    tool = "//sw/host/hsmtool",
)
