# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:autogen.bzl", "autogen_chip_info")
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest", "verilator_params")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

dual_cc_library(
    name = "boot_data",
    srcs = dual_inputs(
        device = ["//sw/lib/sw/device/silicon_creator:boot_data.c"],
        host = ["//sw/lib/sw/device/silicon_creator:mock_boot_data.cc"],
    ),
    hdrs = dual_inputs(
        host = ["//sw/lib/sw/device/silicon_creator:mock_boot_data.h"],
        shared = ["//sw/lib/sw/device/silicon_creator:boot_data.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//sw/lib/sw/device/base:hardened",
            "//sw/lib/sw/device/base:memory",
        ],
        host = [
            "//sw/lib/sw/device/base:global_mock",
            "//sw/lib/sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/lib/sw/device/silicon_creator:error",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/lib/sw/device/base:macros",
        ],
    ),
)

cc_test(
    name = "boot_data_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:boot_data_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":boot_data"),
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "boot_data_functest",
    srcs = ["//sw/lib/sw/device/silicon_creator:boot_data_functest.c"],
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["flaky"],
        # test sometimes times out when run in batches in 3600s
    ),
    deps = [
        ":boot_data",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

cc_test(
    name = "epmp_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:epmp_unittest.cc"],
    deps = [
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "error_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:error_unittest.cc"],
    deps = [
        "//sw/lib/sw/device/silicon_creator:error",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "irq_asm",
    srcs = ["irq_asm.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_darjeeling/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_darjeeling/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/base:multibits",
    ],
)

opentitan_functest(
    name = "irq_asm_functest",
    srcs = ["//sw/lib/sw/device/silicon_creator:irq_asm_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":irq_asm",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

cc_test(
    name = "dbg_print_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:dbg_print_unittest.cc"],
    deps = [
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/lib/sw/device/silicon_creator:dbg_print",
        "//sw/lib/sw/device/silicon_creator:error",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "rom_patch_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:rom_patch_unittest.cc"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/lib/sw/device/base:hardened_memory",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator:rom_patch",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "manifest",
    srcs = dual_inputs(
        device = [
            ":manifest_assert.c",
            "//sw/lib/sw/device/silicon_creator:manifest.c",
        ],
        host = ["//sw/lib/sw/device/silicon_creator:mock_manifest.cc"],
    ),
    hdrs = dual_inputs(
        host = ["//sw/lib/sw/device/silicon_creator:mock_manifest.h"],
        shared = ["//sw/lib/sw/device/silicon_creator:manifest.h"],
    ),
    deps = dual_inputs(
        device = [
            "//sw/top_darjeeling/sw/drivers:flash_ctrl",
        ],
        host = [
            "//sw/lib/sw/device/silicon_creator/testing:rom_test",
            "//sw/lib/sw/device/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/lib/sw/device/silicon_creator:epmp_state",
            "//sw/lib/sw/device/silicon_creator:error",
            "//sw/lib/sw/device/silicon_creator:keymgr_binding",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/lib/sw/device/silicon_creator/sigverify:ecdsa_p256_key",
            "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
            "//sw/lib/sw/device/silicon_creator/sigverify:spx_key",
            "//sw/lib/sw/device/silicon_creator/base:chip",
            "//sw/lib/sw/device/base:macros",
        ],
    ),
)

dual_cc_library(
    name = "manifest_def",
    srcs = dual_inputs(device = [
        "//sw/lib/sw/device/silicon_creator:manifest_def.c",
    ]),
    hdrs = ["//sw/lib/sw/device/silicon_creator:manifest_def.h"],
    target_compatible_with = dual_inputs(device = [OPENTITAN_CPU]),
    deps = [
        ":manifest",
        "//sw/lib/sw/device/base:macros",
    ],
    # The manifest section should be populated anytime this is added as a
    # dependency, even if the manifest is not referenced by software.
    alwayslink = True,
)

filegroup(
    name = "english_breakfast_test_framework_manifest_def_srcs",
    srcs = [
        "//sw/lib/sw/device/silicon_creator:manifest_def.c",
        "//sw/lib/sw/device/silicon_creator:manifest_def.h",
    ],
)

cc_test(
    name = "manifest_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:manifest_unittest.cc"],
    local_defines = ["MANIFEST_UNIT_TEST_"],
    deps = [
        dual_cc_device_library_of(":manifest"),
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

filegroup(
    name = "english_breakfast_test_rom_manifest_srcs",
    srcs = [
        ":manifest_assert.c",
        "//sw/lib/sw/device/silicon_creator:manifest.c",
        "//sw/lib/sw/device/silicon_creator:manifest.h",
    ],
)

autogen_chip_info(name = "chip_info")

dual_cc_library(
    name = "shutdown",
    srcs = dual_inputs(
        device = ["//sw/lib/sw/device/silicon_creator:shutdown.c"],
        host = ["//sw/lib/sw/device/silicon_creator:mock_shutdown.cc"],
    ),
    hdrs = dual_inputs(
        host = ["//sw/lib/sw/device/silicon_creator:mock_shutdown.h"],
        shared = ["//sw/lib/sw/device/silicon_creator:shutdown.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/lib/sw/device/silicon_creator/testing:rom_test",
            "//sw/lib/sw/device/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            ":chip_info",
            "//sw/lib/sw/device/silicon_creator:error",
            "//sw/lib/sw/device/silicon_creator:epmp_defs",
            "//sw/lib/sw/device/base:hardened",
            "//sw/lib/sw/device/base:macros",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//hw/ip/keymgr/data:keymgr_regs",
            "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
            "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
            "//hw/ip/uart/data:uart_regs",
            "//hw/top_darjeeling:alert_handler_regs",
            "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/top_darjeeling/ip/rstmgr/data/autogen:rstmgr_regs",
            "//sw/device/silicon_creator/lib/drivers:alert",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/lib/sw/device/arch:device",
            "//sw/lib/sw/device/base:abs_mmio",
            "//sw/lib/sw/device/base:bitfield",
            "//sw/lib/sw/device/base:csr",
            "//sw/lib/sw/device/base:memory",
            "//sw/lib/sw/device/base:multibits",
            "//sw/lib/sw/device/base:stdasm",
            "//sw/top_darjeeling/sw/drivers:flash_ctrl",
            "//sw/top_darjeeling/sw/drivers:keymgr",
            "//sw/top_darjeeling/sw/drivers:lc_ctrl",
            "//sw/top_darjeeling/sw/drivers:otp_ctrl",
            "//sw/top_darjeeling/sw/drivers:rstmgr",
            "//sw/top_darjeeling/sw/drivers:rv_core_ibex",
            "//sw/top_darjeeling/sw/drivers:sram_ctrl",
            "//sw/top_darjeeling/sw/drivers:uart",
        ],
    ),
)

cc_test(
    name = "shutdown_unittest",
    srcs = ["shutdown_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":shutdown"),
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "crc32_unittest",
    srcs = ["//sw/lib/sw/device/silicon_creator:crc32_unittest.cc"],
    deps = [
        dual_cc_device_library_of("//sw/lib/sw/device/silicon_creator:crc32"),
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "crc32_functest",
    srcs = ["//sw/lib/sw/device/silicon_creator:crc32_functest.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator:crc32",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "crc32_perftest",
    srcs = ["//sw/lib/sw/device/silicon_creator:crc32_perftest.c"],
    cw310 = cw310_params(
        tags = [
            "manual",
        ],
    ),
    targets = ["cw310_test_rom"],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator:crc32",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)
