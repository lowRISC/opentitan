# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rsa",
    srcs = [
        "darjeeling_a0_dev_0.h",
        "darjeeling_a0_dev_1.h",
        "darjeeling_a0_prod_0.h",
        "darjeeling_a0_prod_1.h",
        "darjeeling_a0_prod_2.h",
        "darjeeling_a0_test_0.h",
        "darjeeling_a0_test_1.h",
        "sigverify_rsa_keys_real.c",
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
        "sigverify_rsa_keys_real_unittest.cc",
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
    name = "darjeeling_a0_test_0",
    srcs = ["darjeeling_a0_test_0.der"],
)

filegroup(
    name = "darjeeling_a0_test_1",
    srcs = ["darjeeling_a0_test_1.der"],
)

filegroup(
    name = "darjeeling_a0_dev_0",
    srcs = ["darjeeling_a0_dev_0.der"],
)

filegroup(
    name = "darjeeling_a0_dev_1",
    srcs = ["darjeeling_a0_dev_1.der"],
)

filegroup(
    name = "darjeeling_a0_prod_0",
    srcs = ["darjeeling_a0_prod_0.der"],
)

filegroup(
    name = "darjeeling_a0_prod_1",
    srcs = ["darjeeling_a0_prod_1.der"],
)

filegroup(
    name = "darjeeling_a0_prod_2",
    srcs = ["darjeeling_a0_prod_2.der"],
)
