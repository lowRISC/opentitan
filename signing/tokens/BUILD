# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "signing_tool")

package(default_visibility = ["//visibility:public"])

signing_tool(
    name = "local",
    location = "local",
    tool = "//sw/host/opentitantool",
)

signing_tool(
    name = "nitrokey",
    data = ["@sc_hsm//:gen_dir"],
    env = {
        "HSMTOOL_MODULE": "$(location @sc_hsm//:gen_dir)/lib/libsc-hsm-pkcs11.so",
    },
    location = "token",
    tool = "//sw/host/hsmtool",
)
