# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

dual_cc_library(
    name = "boot_data",
    srcs = dual_inputs(
        device = ["boot_data.c"],
        host = ["mock_boot_data.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_boot_data.h"],
        shared = ["boot_data.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:memory",
        ],
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":error",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
        ],
    ),
)

opentitan_functest(
    name = "boot_data_functest",
    srcs = ["boot_data_functest.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        ":boot_data",
        ":test_main",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
    ],
)

cc_library(
    name = "cfi",
    hdrs = [
        "cfi.h",
    ],
    deps = [
        "//sw/device/lib/base:hardened",
    ],
)

cc_library(
    name = "epmp",
    srcs = ["epmp.c"],
    hdrs = [
        "epmp.h",
        "epmp_defs.h",
    ],
    deps = [
        ":error",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:hardened",
    ],
)

cc_test(
    name = "epmp_unittest",
    srcs = ["epmp_unittest.cc"],
    deps = [
        ":epmp",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "epmp_test_unlock",
    srcs = ["epmp_test_unlock.c"],
    hdrs = ["epmp_test_unlock.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":epmp",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:csr",
    ],
)

cc_library(
    name = "error",
    srcs = ["absl_status.h"],
    hdrs = ["error.h"],
    deps = [
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
    ],
)

cc_test(
    name = "error_unittest",
    srcs = ["error_unittest.cc"],
    deps = [
        ":error",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "irq_asm",
    srcs = ["irq_asm.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:multibits",
    ],
)

opentitan_functest(
    name = "irq_asm_functest",
    srcs = ["irq_asm_functest.c"],
    deps = [
        ":error",
        ":irq_asm",
        ":test_main",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
    ],
)

cc_library(
    name = "keymgr_binding",
    hdrs = ["keymgr_binding_value.h"],
)

cc_library(
    name = "log",
    srcs = ["log.c"],
    hdrs = ["log.h"],
    deps = [
        ":error",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_test(
    name = "log_unittest",
    srcs = ["log_unittest.cc"],
    deps = [
        ":error",
        ":log",
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "manifest_size",
    hdrs = ["manifest_size.h"],
)

dual_cc_library(
    name = "manifest",
    srcs = dual_inputs(
        device = ["manifest.c"],
        host = ["mock_manifest.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_manifest.h"],
        shared = ["manifest.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":epmp",
            ":error",
            ":keymgr_binding",
            ":manifest_size",
            ":sigverify_internal",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
        ],
    ),
)

cc_test(
    name = "manifest_unittest",
    srcs = ["manifest_unittest.cc"],
    local_defines = ["MANIFEST_UNIT_TEST_"],
    deps = [
        dual_cc_device_library_of(":manifest"),
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn_util",
    srcs = ["otbn_util.c"],
    hdrs = ["otbn_util.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib/drivers:otbn",
    ],
)

dual_cc_library(
    name = "shutdown",
    srcs = dual_inputs(
        device = ["shutdown.c"],
        host = ["mock_shutdown.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_shutdown.h"],
        shared = ["shutdown.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":error",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//hw/ip/keymgr/data:keymgr_regs",
            "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
            "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
            "//hw/ip/uart/data:uart_regs",
            "//hw/top_earlgrey:alert_handler_regs",
            "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/arch:device",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:csr",
            "//sw/device/lib/base:memory",
            "//sw/device/lib/base:multibits",
            "//sw/device/lib/base:stdasm",
            "//sw/device/silicon_creator/lib/drivers:alert",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    ),
)

cc_test(
    name = "shutdown_unittest",
    srcs = ["shutdown_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":shutdown"),
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sigverify_internal",
    hdrs = [
        "sigverify_mod_exp.h",
        "sigverify_rsa_key.h",
    ],
    deps = [
        ":error",
    ],
)

cc_library(
    name = "sigverify_intf",
    hdrs = ["sigverify.h"],
    deps = [
        ":error",
        ":manifest",
        ":sigverify_internal",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
    ],
)

cc_library(
    name = "sigverify",
    srcs = ["sigverify.c"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":sigverify_internal",
        ":sigverify_intf",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

filegroup(
    name = "sigverify_src_for_keys_unittest",
    srcs = ["sigverify.c"],
)

cc_test(
    name = "sigverify_unittest",
    srcs = [
        "sigverify.c",
        "sigverify_unittest.cc",
    ],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        ":mock_sigverify",
        ":sigverify_intf",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
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
            "verilator",
        ],
    ),
    deps = [
        ":sigverify",
        ":sigverify_intf",
        ":sigverify_mod_exp_ibex",
        ":sigverify_mod_exp_otbn",
        ":test_main",
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
            "verilator",
        ],
    ),
    deps = [
        ":sigverify",
        ":sigverify_mod_exp_ibex",
        ":sigverify_mod_exp_otbn",
        ":sigverify_testvectors",
        ":test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "sigverify_mod_exp_ibex",
    srcs = ["sigverify_mod_exp_ibex.c"],
    deps = [
        ":sigverify_internal",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
    ],
)

cc_library(
    name = "sigverify_mod_exp_otbn",
    srcs = ["sigverify_mod_exp_otbn.c"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":error",
        ":otbn_util",
        ":sigverify_internal",
        "//sw/device/silicon_creator/lib/drivers:otbn",
        "//sw/otbn/crypto:run_rsa_verify_3072_rr_modexp",
    ],
)

cc_library(
    name = "sigverify_testvectors",
    hdrs = [
        "sigverify_tests/sigverify_testvectors.h",
    ],
    deps = [
    ],
)

opentitan_functest(
    name = "sigverify_mod_exp_ibex_functest",
    srcs = ["sigverify_mod_exp_ibex_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
            "verilator",
        ],
    ),
    deps = [
        ":sigverify_mod_exp_ibex",
        ":sigverify_testvectors",
        ":test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

opentitan_functest(
    name = "sigverify_mod_exp_otbn_functest",
    srcs = ["sigverify_mod_exp_otbn_functest.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = [
            "manual",
            "verilator",
        ],
    ),
    deps = [
        ":sigverify_mod_exp_otbn",
        ":sigverify_testvectors",
        ":test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "mock_sigverify",
    testonly = True,
    hdrs = [
        "mock_sigverify_mod_exp_ibex.h",
        "mock_sigverify_mod_exp_otbn.h",
    ],
    deps = [
        ":sigverify_internal",
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "sigverify_mod_exp_ibex_unittest",
    srcs = ["sigverify_mod_exp_ibex_unittest.cc"],
    deps = [
        ":sigverify_internal",
        ":sigverify_intf",
        ":sigverify_mod_exp_ibex",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "test_main",
    hdrs = ["test_main.h"],
    deps = [
        ":error",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf",
    ],
)
