# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "test_public_keys",
    hdrs = [
        "test_key_0_rsa_3072_exp_f4.h",
    ],
)

filegroup(
    name = "test_private_key_0",
    srcs = ["test_key_0_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "unauthorized_private_key_0",
    srcs = ["unauthorized_rsa_3072_exp_f4.der"],
)
