# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load(
    "//rules:cross_platform.bzl",
    "dual_cc_device_library_of",
    "dual_cc_library",
    "dual_inputs",
)
load("//rules:otbn.bzl", "otbn_insn_count_range")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "ecdsa_p256_key",
    srcs = ["ecdsa_p256_key.c"],
    hdrs = ["ecdsa_p256_key.h"],
    deps = [
        "//sw/lib/sw/device/base:macros",
    ],
)

cc_library(
    name = "rsa_key",
    srcs = ["rsa_key.c"],
    hdrs = ["rsa_key.h"],
    deps = [
        "//sw/lib/sw/device/base:macros",
    ],
)

cc_library(
    name = "spx_key",
    srcs = ["spx_key.c"],
    hdrs = ["spx_key.h"],
    deps = [
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:params",
    ],
)

dual_cc_library(
    name = "mod_exp_ibex",
    srcs = dual_inputs(
        device = ["mod_exp_ibex.c"],
        host = ["mock_mod_exp_ibex.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_mod_exp_ibex.h"],
        shared = ["mod_exp_ibex.h"],
    ),
    deps = dual_inputs(
        device = [
            "//sw/lib/sw/device/base:macros",
        ],
        host = [
            "//sw/lib/sw/device/silicon_creator/testing:rom_test",
            "//sw/lib/sw/device/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            ":rsa_key",
            "//sw/lib/sw/device/silicon_creator:error",
        ],
    ),
)

alias(
    name = "mod_exp_ibex_device_library",
    actual = dual_cc_device_library_of(":mod_exp_ibex"),
)

cc_test(
    name = "mod_exp_ibex_unittest",
    srcs = ["mod_exp_ibex_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":mod_exp_ibex"),
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "mod_exp_otbn",
    srcs = dual_inputs(
        device = ["mod_exp_otbn.c"],
        host = ["mock_mod_exp_otbn.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_mod_exp_otbn.h"],
        shared = ["mod_exp_otbn.h"],
    ),
    target_compatible_with = dual_inputs(
        # This target uses OTBN pointers internally, so it cannot
        # work host-side.
        device = [OPENTITAN_CPU],
    ),
    deps = dual_inputs(
        device = [
            "//sw/device/silicon_creator/lib/drivers:otbn",
            "//sw/lib/sw/device/base:macros",
            "//sw/lib/sw/device/base:memory",
            "//sw/otbn/crypto:run_rsa_verify_3072_rr_modexp",
        ],
        host = [
            "//sw/lib/sw/device/silicon_creator/testing:rom_test",
            "//sw/lib/sw/device/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            ":rsa_key",
            "//sw/lib/sw/device/silicon_creator:error",
        ],
    ),
)

# This rule runs the instruction-counting script for OTBN and gets the expected
# min/max instruction counts.
otbn_insn_count_range(
    name = "mod_exp_otbn_insn_count_range",
    deps = [
        "//sw/otbn/crypto:run_rsa_verify_3072_rr_modexp",
    ],
)

# Check the OTBN instruction count in mod_exp_otbn.h
sh_test(
    name = "mod_exp_otbn_insn_count_check",
    size = "small",
    srcs = ["mod_exp_otbn_insn_count_check.sh"],
    args = [
        "$(location :mod_exp_otbn_insn_count_range)",
        "$(location mod_exp_otbn.h)",
    ],
    data = [
        "mod_exp_otbn.h",
        ":mod_exp_otbn_insn_count_range",
    ],
)

cc_library(
    name = "ecdsa_p256_verify",
    srcs = ["ecdsa_p256_verify.c"],
    hdrs = ["ecdsa_p256_verify.h"],
    deps = [
        ":ecdsa_p256_key",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/silicon_creator:otbn_boot_services",
    ],
)

cc_library(
    name = "rsa_verify",
    srcs = ["rsa_verify.c"],
    hdrs = ["rsa_verify.h"],
    deps = [
        ":mod_exp_ibex",
        ":mod_exp_otbn",
        ":rsa_key",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/lib/sw/device/base:hardened",
    ],
)

cc_library(
    name = "spx_verify",
    srcs = ["spx_verify.c"],
    hdrs = ["spx_verify.h"],
    deps = [
        ":spx_key",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:verify",
    ],
)

cc_library(
    name = "usage_constraints",
    srcs = ["usage_constraints.c"],
    hdrs = ["usage_constraints.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/silicon_creator:manifest",
    ],
)

cc_library(
    name = "flash_exec",
    hdrs = ["flash_exec.h"],
    deps = [
        ":rsa_verify",
        ":spx_verify",
    ],
)

cc_library(
    name = "sigverify",
    hdrs = ["sigverify.h"],
    deps = [
        ":rsa_verify",
        ":spx_verify",
        ":usage_constraints",
    ],
)

cc_test(
    name = "sigverify_unittest",
    srcs = ["sigverify_unittest.cc"],
    deps = [
        ":sigverify",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

exports_files([
    "mod_exp_ibex_functest.c",
    "mod_exp_ibex_functest.c",
    "mod_exp_otbn_functest.c",
    "mod_exp_otbn_functest.c",
    "ecdsa_p256_verify_functest.c",
    "rsa_verify_functest.c",
    "spx_verify_functest.c",
    "flash_exec_unittest.cc",
    "sigverify_dynamic_functest.c",
    "sigverify_dynamic_functest.c",
])
