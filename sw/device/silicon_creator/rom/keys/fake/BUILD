# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "fake",
    srcs = [
        "sigverify_rsa_keys_fake.c",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key.h",
        "//sw/device/silicon_creator/rom:sigverify_keys_ptrs.h",
    ],
    hdrs = [
        "dev_key_0_rsa_3072_exp_f4.h",
        "prod_key_0_rsa_3072_exp_f4.h",
        "test_key_0_rsa_3072_exp_f4.h",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:macros",
    ],
)

filegroup(
    name = "test_private_key_0",
    srcs = ["test_key_0_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "dev_private_key_0",
    srcs = ["dev_key_0_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "prod_private_key_0",
    srcs = ["prod_key_0_rsa_3072_exp_f4.der"],
)
