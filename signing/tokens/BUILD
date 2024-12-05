# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "HOME")
load("//rules:signing.bzl", "signing_tool")

package(default_visibility = ["//visibility:public"])

signing_tool(
    name = "local",
    location = "local",
    tool = "//sw/host/opentitantool",
)

signing_tool(
    name = "nitrokey",
    data = ["@opensc//:gen_dir"],
    env = {
        "LD_LIBRARY_PATH": "$(location @opensc//:gen_dir)/lib",
        "HSMTOOL_MODULE": "$(location @opensc//:gen_dir)/lib/opensc-pkcs11.so",
        "HSMTOOL_SPX_MODULE": "pkcs11-ef",
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
        "HOME": HOME,
        "HSMTOOL_MODULE": "$(location @cloud_kms_hsm//:libkmsp11)",
        "KMS_PKCS11_CONFIG": "$(location earlgrey_z1_sival.yaml)",
    },
    location = "token",
    tool = "//sw/host/hsmtool",
)
