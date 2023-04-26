# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")
load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
)
load("//rules:otbn.bzl", "otbn_insn_count_range")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rsa_key",
    srcs = ["rsa_key.c"],
    hdrs = ["rsa_key.h"],
)

cc_library(
    name = "spx_key",
    srcs = ["spx_key.c"],
    hdrs = ["spx_key.h"],
    deps = ["//sw/device/silicon_creator/lib/sigverify/sphincsplus:params"],
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
            "//sw/device/lib/base:macros",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":rsa_key",
            "//sw/device/silicon_creator/lib:error",
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

opentitan_functest(
    name = "mod_exp_ibex_functest_hardcoded",
    srcs = ["mod_exp_ibex_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":mod_exp_ibex",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_hardcoded",
    ],
)

opentitan_functest(
    name = "mod_exp_ibex_functest_wycheproof",
    srcs = ["mod_exp_ibex_functest.c"],
    cw310 = cw310_params(
        timeout = "long",
    ),
    targets = ["cw310_test_rom"],  # Test set is too large to run in simulation
    deps = [
        ":mod_exp_ibex",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
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
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:memory",
            "//sw/device/silicon_creator/lib/drivers:otbn",
            "//sw/otbn/crypto:run_rsa_verify_3072_rr_modexp",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":rsa_key",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

opentitan_functest(
    name = "mod_exp_otbn_functest_hardcoded",
    srcs = ["mod_exp_otbn_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":mod_exp_otbn",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_hardcoded",
    ],
)

opentitan_functest(
    name = "mod_exp_otbn_functest_wycheproof",
    srcs = ["mod_exp_otbn_functest.c"],
    targets = [
        "cw310_test_rom",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":mod_exp_otbn",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
    ],
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
    name = "rsa_verify",
    srcs = ["rsa_verify.c"],
    hdrs = ["rsa_verify.h"],
    deps = [
        ":mod_exp_ibex",
        ":mod_exp_otbn",
        ":rsa_key",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

opentitan_functest(
    name = "rsa_verify_functest",
    srcs = ["rsa_verify_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":rsa_verify",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "spx_verify",
    srcs = ["spx_verify.c"],
    hdrs = ["spx_verify.h"],
    deps = [
        ":spx_key",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_functest(
    name = "spx_verify_functest",
    srcs = ["spx_verify_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":spx_verify",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "usage_constraints",
    srcs = ["usage_constraints.c"],
    hdrs = ["usage_constraints.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/drivers:otp",
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

cc_test(
    name = "flash_exec_unittest",
    srcs = ["flash_exec_unittest.cc"],
    deps = [
        ":flash_exec",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
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
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "sigverify_dynamic_functest_hardcoded",
    srcs = ["sigverify_dynamic_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":sigverify",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_hardcoded",
    ],
)

opentitan_functest(
    name = "sigverify_dynamic_functest_wycheproof",
    srcs = ["sigverify_dynamic_functest.c"],
    cw310 = cw310_params(
        timeout = "long",
    ),
    targets = ["cw310_test_rom"],  # Test set is too large to run in simulation
    deps = [
        ":sigverify",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
    ],
)
