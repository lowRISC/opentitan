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
        device = ["boot_data.c"],
        host = ["mock_boot_data.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_boot_data.h"],
        shared = ["boot_data.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:memory",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":error",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    ),
)

cc_test(
    name = "boot_data_unittest",
    srcs = ["boot_data_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":boot_data"),
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "boot_data_functest",
    srcs = ["boot_data_functest.c"],
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["flaky"],
        # test sometimes times out when run in batches in 3600s
    ),
    deps = [
        ":boot_data",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:ottf_main",
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
    name = "epmp_defs",
    hdrs = [
        "epmp_defs.h",
    ],
)

cc_library(
    name = "epmp_state",
    srcs = ["epmp_state.c"],
    hdrs = [
        "epmp_state.h",
    ],
    deps = [
        ":epmp_defs",
        ":error",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:hardened",
    ],
)

cc_test(
    name = "epmp_unittest",
    srcs = ["epmp_unittest.cc"],
    deps = [
        ":epmp_state",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "epmp_test_unlock",
    srcs = ["epmp_test_unlock.c"],
    hdrs = ["epmp_test_unlock.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":epmp_state",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:csr",
    ],
)

cc_library(
    name = "error",
    hdrs = ["error.h"],
    deps = [
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base/internal:status",
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
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:multibits",
    ],
)

opentitan_functest(
    name = "irq_asm_functest",
    srcs = ["irq_asm_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":error",
        ":irq_asm",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
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
    name = "rom_print",
    srcs = ["rom_print.c"],
    hdrs = ["rom_print.h"],
    deps = [
        ":error",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_test(
    name = "rom_print_unittest",
    srcs = ["rom_print_unittest.cc"],
    deps = [
        ":error",
        ":rom_print",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "@googletest//:gtest_main",
    ],
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
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":epmp_state",
            ":error",
            ":keymgr_binding",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/sigverify:rsa_key",
            "//sw/device/silicon_creator/lib/sigverify:spx_key",
            "//sw/device/silicon_creator/lib/base:chip",
        ],
    ),
)

dual_cc_library(
    name = "manifest_def",
    srcs = dual_inputs(device = ["manifest_def.c"]),
    hdrs = ["manifest_def.h"],
    target_compatible_with = dual_inputs(device = [OPENTITAN_CPU]),
    deps = [
        ":manifest",
        "//sw/device/lib/base:macros",
    ],
    # The manifest section should be populated anytime this is added as a
    # dependency, even if the manifest is not referenced by software.
    alwayslink = True,
)

filegroup(
    name = "english_breakfast_test_framework_manifest_def_srcs",
    srcs = [
        "manifest_def.c",
        "manifest_def.h",
    ],
)

cc_test(
    name = "manifest_unittest",
    srcs = ["manifest_unittest.cc"],
    local_defines = ["MANIFEST_UNIT_TEST_"],
    deps = [
        dual_cc_device_library_of(":manifest"),
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

filegroup(
    name = "english_breakfast_test_rom_manifest_srcs",
    srcs = [
        "manifest.c",
        "manifest.h",
    ],
)

autogen_chip_info(name = "chip_info")

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
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":chip_info",
            ":error",
            ":epmp_defs",
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
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "crc32",
    srcs = dual_inputs(
        device = ["crc32.c"],
        host = ["mock_crc32.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_crc32.h"],
        shared = ["crc32.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:memory",
            "//sw/device/lib/base:macros",
        ],
    ),
)

cc_test(
    name = "crc32_unittest",
    srcs = ["crc32_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":crc32"),
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "crc32_functest",
    srcs = ["crc32_functest.c"],
    deps = [
        ":crc32",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "crc32_perftest",
    srcs = ["crc32_perftest.c"],
    cw310 = cw310_params(
        tags = [
            "manual",
        ],
    ),
    targets = ["cw310_test_rom"],
    deps = [
        ":crc32",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
    ],
)
