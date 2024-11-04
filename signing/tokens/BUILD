# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")
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

signing_tool(
    name = "cloud_kms_sival",
    data = [
        "earlgrey_z1_sival.yaml",
        "@cloud_kms_hsm//:libkmsp11",
    ],
    env = {
        # The Cloud KMS PKCS11 provider needs to know where the user's home
        # is in order to load the gclould credentials.
        "HOME": ENV["HOME"],
        "HSMTOOL_MODULE": "$(location @cloud_kms_hsm//:libkmsp11)",
        "KMS_PKCS11_CONFIG": "$(location earlgrey_z1_sival.yaml)",
    },
    location = "token",
    tool = "//sw/host/hsmtool",
)
