# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rsa",
    srcs = [
        "dev_key_0_rsa_3072_exp_f4.h",
        "dev_key_1_rsa_3072_exp_f4.h",
        "prod_key_0_rsa_3072_exp_f4.h",
        "prod_key_1_rsa_3072_exp_f4.h",
        "prod_key_2_rsa_3072_exp_f4.h",
        "sigverify_rsa_keys_fake.c",
        "test_key_0_rsa_3072_exp_f4.h",
        "test_key_1_rsa_3072_exp_f4.h",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/rom:sigverify_key_types",
        "//sw/device/silicon_creator/rom:sigverify_keys",
        "//sw/lib/sw/device/base:macros",
    ],
)

# Flatten //sw/lib/sw/device/silicon_creator/sigverify:rsa_verify to exclude mock_mod_exp_ibex
cc_test(
    name = "rsa_unittest",
    srcs = [
        "sigverify_rsa_keys_fake_unittest.cc",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_verify.c",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_verify.h",
    ],
    deps = [
        ":rsa",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/rom:sigverify_keys",
        "//sw/device/silicon_creator/rom:sigverify_keys_rsa",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_ibex_device_library",
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_otbn",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

filegroup(
    name = "test_private_key_0",
    srcs = ["test_key_0_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "test_private_key_1",
    srcs = ["test_key_1_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "dev_private_key_0",
    srcs = ["dev_key_0_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "dev_private_key_1",
    srcs = ["dev_key_1_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "prod_private_key_0",
    srcs = ["prod_key_0_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "prod_private_key_1",
    srcs = ["prod_key_1_rsa_3072_exp_f4.der"],
)

filegroup(
    name = "prod_private_key_2",
    srcs = ["prod_key_2_rsa_3072_exp_f4.der"],
)
