# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "includes",
    hdrs = [
        "appkey_dev_0.h",
        "appkey_prod_0.h",
        "appkey_test_0.h",
        "earlgrey_z1_prodc_1.h",
        "ownership_activate_key.h",
        "ownership_owner_key.h",
        "ownership_unlock_key.h",
    ],
)

cc_library(
    name = "keys",
    srcs = [
        "sigverify_rsa_keys_prodc.c",
        "//sw/device/silicon_creator/rom_ext:sigverify_keys.h",
    ],
    hdrs = [
        "earlgrey_z1_prodc_1.h",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/sigverify",
    ],
)

cc_test(
    name = "keys_unittest",
    srcs = [
        "sigverify_rsa_keys_prodc_unittest.cc",
        "//sw/device/silicon_creator/lib/sigverify:rsa_verify.c",
        "//sw/device/silicon_creator/lib/sigverify:rsa_verify.h",
    ],
    deps = [
        ":keys",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:mod_exp_ibex_device_library",
        "//sw/device/silicon_creator/lib/sigverify:mod_exp_otbn",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        "//sw/device/silicon_creator/lib/sigverify:rsa_verify",
        "//sw/device/silicon_creator/rom_ext:sigverify_keys",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

keyset(
    name = "keyset",
    build_setting_default = "",
    keys = {
        "earlgrey_z1_prodc_1.der": "earlgrey_z1_prodc_1",
        "appkey_dev_0.der": "appkey_dev_0",
        "appkey_prod_0.der": "appkey_prod_0",
        "appkey_test_0.der": "appkey_test_0",
    },
    profile = "earlgrey_z1_prodc",
    tool = "//signing:token",
)
