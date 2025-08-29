# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:signing.bzl", "keyset")

filegroup(
    name = "unauthorized_0_spx",
    srcs = ["unauthorized_0_spx.pem"],
)

keyset(
    name = "spx_keyset",
    build_setting_default = "",
    keys = {
        "unauthorized_0_spx.pem": "unauthorized_key_0",
    },
    profile = "local",
    tool = "//signing/tokens:local",
)
