# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rsa",
    srcs = [
        "sigverify_rsa_keys_real.c",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/rom:sigverify_keys",
    ],
)

# Flatten //sw/device/silicon_creator/lib/sigverify:rsa_verify to exclude mock_mod_exp_ibex
cc_test(
    name = "rsa_unittest",
    srcs = [
        "sigverify_rsa_keys_real_unittest.cc",
        "//sw/device/silicon_creator/lib/sigverify:rsa_verify.c",
        "//sw/device/silicon_creator/lib/sigverify:rsa_verify.h",
    ],
    deps = [
        ":rsa",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:mod_exp_ibex_device_library",
        "//sw/device/silicon_creator/lib/sigverify:mod_exp_otbn",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        "//sw/device/silicon_creator/rom:sigverify_keys",
        "//sw/device/silicon_creator/rom:sigverify_keys_rsa",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

filegroup(
    name = "test_private_key_0",
    srcs = [],
)

filegroup(
    name = "test_private_key_1",
    srcs = [],
)

filegroup(
    name = "dev_private_key_0",
    srcs = [],
)

filegroup(
    name = "dev_private_key_1",
    srcs = [],
)

filegroup(
    name = "prod_private_key_0",
    srcs = [],
)

filegroup(
    name = "prod_private_key_1",
    srcs = [],
)

filegroup(
    name = "prod_private_key_2",
    srcs = [],
)
