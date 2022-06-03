# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")
load(
    "//rules:opentitan_test.bzl",
    "opentitan_functest",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rsa_key",
    hdrs = ["rsa_key.h"],
)

cc_library(
    name = "testvectors",
    hdrs = ["sigverify_tests/sigverify_testvectors.h"],
)

dual_cc_library(
    name = "mod_exp_ibex",
    srcs = dual_inputs(
        device = ["mod_exp_ibex.c"],
        host = ["mod_exp_ibex_mock.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mod_exp_ibex_mock.h"],
        shared = ["mod_exp_ibex.h"],
    ),
    deps = dual_inputs(
        device = [
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:memory",
        ],
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":rsa_key",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
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
    name = "mod_exp_ibex_functest",
    srcs = ["mod_exp_ibex_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":mod_exp_ibex",
        ":testvectors",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

dual_cc_library(
    name = "mod_exp_otbn",
    srcs = dual_inputs(
        device = ["mod_exp_otbn.c"],
        host = ["mod_exp_otbn_mock.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mod_exp_otbn_mock.h"],
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
            "//sw/device/silicon_creator/lib:otbn_util",
            "//sw/otbn/crypto:run_rsa_verify_3072_rr_modexp",
        ],
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":rsa_key",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

opentitan_functest(
    name = "mod_exp_otbn_functest",
    srcs = ["mod_exp_otbn_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":mod_exp_otbn",
        ":testvectors",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

# Common inputs for sigverify.c; we publish two variants of this
# library, so factoring this out simplifies the build.
cc_library(
    name = "sigverify_inner",
    srcs = ["sigverify.c"],
    hdrs = ["sigverify.h"],
    visibility = ["//visibility:private"],
    deps = [
        ":mod_exp_ibex",
        ":mod_exp_otbn",
        ":rsa_key",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

cc_library(
    name = "sigverify",
    deps = [
        ":mod_exp_ibex",
        ":mod_exp_otbn",
        ":sigverify_inner",
    ],
)

cc_library(
    name = "sigverify_without_mod_exp_ibex_mock",
    visibility = ["//sw/device/silicon_creator/mask_rom:__pkg__"],
    deps = [
        dual_cc_device_library_of(":mod_exp_ibex"),
        ":mod_exp_otbn",
        ":sigverify_inner",
    ],
)

cc_test(
    name = "sigverify_unittest",
    srcs = ["sigverify_unittest.cc"],
    deps = [
        ":sigverify",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "sigverify_functest",
    srcs = ["sigverify_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":sigverify",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

opentitan_functest(
    name = "sigverify_dynamic_functest",
    srcs = ["sigverify_dynamic_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
        ],
    ),
    deps = [
        ":sigverify",
        ":testvectors",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)
