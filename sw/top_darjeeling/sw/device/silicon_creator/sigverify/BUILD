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

opentitan_functest(
    name = "mod_exp_ibex_functest_hardcoded",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_ibex_functest.c",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_ibex",
        "//sw/lib/sw/device/silicon_creator/sigverify/sigverify_tests:sigverify_testvectors_hardcoded",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "mod_exp_ibex_functest_wycheproof",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_ibex_functest.c",
    ],
    cw310 = cw310_params(
        timeout = "long",
    ),
    targets = ["cw310_test_rom"],  # Test set is too large to run in simulation
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_ibex",
        "//sw/lib/sw/device/silicon_creator/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "mod_exp_otbn_functest_hardcoded",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_otbn_functest.c",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_otbn",
        "//sw/lib/sw/device/silicon_creator/sigverify/sigverify_tests:sigverify_testvectors_hardcoded",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "mod_exp_otbn_functest_wycheproof",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_otbn_functest.c",
    ],
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify:mod_exp_otbn",
        "//sw/lib/sw/device/silicon_creator/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "rsa_verify_functest",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_verify_functest.c",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_verify",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "spx_verify_functest",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:spx_verify_functest.c",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/sigverify:spx_verify",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "ecdsa_p256_verify_functest",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:ecdsa_p256_verify_functest.c",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/sigverify:ecdsa_p256_verify",
        "//sw/otbn/crypto:boot",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

cc_test(
    name = "flash_exec_unittest",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:flash_exec_unittest.cc",
    ],
    deps = [
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/lib/sw/device/silicon_creator/sigverify:flash_exec",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "sigverify_dynamic_functest_hardcoded",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:sigverify_dynamic_functest.c",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/lib/sw/device/silicon_creator/sigverify/sigverify_tests:sigverify_testvectors_hardcoded",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "sigverify_dynamic_functest_wycheproof",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify:sigverify_dynamic_functest.c",
    ],
    cw310 = cw310_params(
        timeout = "long",
    ),
    targets = ["cw310_test_rom"],  # Test set is too large to run in simulation
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/lib/sw/device/silicon_creator/sigverify/sigverify_tests:sigverify_testvectors_wycheproof",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)
