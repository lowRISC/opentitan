# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:cross_platform.bzl",
    "dual_cc_device_library_of",
    "dual_cc_library",
    "dual_inputs",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "fpga_params",
    "opentitan_test",
    "verilator_params",
)
load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "ecdsa_p256_key",
    srcs = ["ecdsa_p256_key.c"],
    hdrs = ["ecdsa_p256_key.h"],
    deps = [
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "rsa_key",
    srcs = ["rsa_key.c"],
    hdrs = ["rsa_key.h"],
    deps = [
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "spx_key",
    srcs = ["spx_key.c"],
    hdrs = ["spx_key.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:params",
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

opentitan_test(
    name = "mod_exp_ibex_functest_hardcoded",
    srcs = ["mod_exp_ibex_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
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

opentitan_test(
    name = "mod_exp_ibex_functest_wycheproof",
    srcs = ["mod_exp_ibex_functest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
    fpga = fpga_params(
        timeout = "long",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        ":mod_exp_ibex",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
    ],
)

cc_library(
    name = "ecdsa_p256_verify",
    srcs = ["ecdsa_p256_verify.c"],
    hdrs = ["ecdsa_p256_verify.h"],
    deps = [
        ":ecdsa_p256_key",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)

opentitan_test(
    name = "ecdsa_p256_verify_functest",
    srcs = ["ecdsa_p256_verify_functest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:fpga_cw340_test_rom": None,
        },
    ),
    deps = [
        ":ecdsa_p256_verify",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "rsa_verify",
    srcs = ["rsa_verify.c"],
    hdrs = ["rsa_verify.h"],
    deps = [
        ":mod_exp_ibex",
        ":rsa_key",
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

opentitan_test(
    name = "rsa_verify_functest",
    srcs = ["rsa_verify_functest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
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
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "spx_verify_functest",
    srcs = ["spx_verify_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
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
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
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
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sigverify",
    hdrs = ["sigverify.h"],
    deps = [
        ":ecdsa_p256_verify",
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

opentitan_test(
    name = "sigverify_dynamic_functest_hardcoded",
    srcs = ["sigverify_dynamic_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
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

opentitan_test(
    name = "sigverify_dynamic_functest_wycheproof",
    srcs = ["sigverify_dynamic_functest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # Test set is too large as ROM_EXT
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
    fpga = fpga_params(
        timeout = "long",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        ":sigverify",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
    ],
)
