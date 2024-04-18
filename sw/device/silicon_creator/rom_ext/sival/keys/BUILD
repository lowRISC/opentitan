# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "keys",
    srcs = [
        "sigverify_rsa_keys_sival.c",
        "//sw/device/silicon_creator/rom_ext:sigverify_keys.h",
    ],
    hdrs = [
        "earlgrey_z0_sival_1.h",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/sigverify",
    ],
)

cc_test(
    name = "keys_unittest",
    srcs = [
        "sigverify_rsa_keys_sival_unittest.cc",
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
        "earlgrey_z0_sival_1.der": "earlgrey_z0_sival_1",
    },
    profile = "earlgrey_z0_sival",
    tool = "//signing:token",
)
