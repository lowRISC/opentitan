# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_binary", "opentitan_functest", "verilator_params")

cc_library(
    name = "alert",
    srcs = ["alert.c"],
    hdrs = ["alert.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "mock_alert",
    testonly = True,
    hdrs = [
        "alert.h",
        "mock_alert.h",
    ],
    deps = [
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "alert_unittest",
    srcs = [
        "alert.h",
        "alert.c",
        "alert_unittest.cc",
    ],
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:mock_sec_mmio",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "alert_functest",
    srcs = ["alert_functest.c"],
    deps = [
        ":alert",
        ":rstmgr",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "flash_ctrl",
    srcs = ["flash_ctrl.c"],
    hdrs = ["flash_ctrl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

cc_test(
    name = "flash_ctrl_unittest",
    srcs = [
        "flash_ctrl.c",
        "flash_ctrl.h",
        "flash_ctrl_unittest.cc",
    ],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:mock_sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:mock_otp",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_library(
    name = "mock_hmac",
    testonly = True,
    hdrs = ["mock_hmac.h"],
    deps = [
        ":hmac",
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "hmac_unittest",
    srcs = ["hmac_unittest.cc"],
    deps = [
        ":hmac",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "hmac_functest",
    srcs = ["hmac_functest.c"],
    deps = [
        ":hmac",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:test_main",
    ],
)

cc_library(
    name = "keymgr",
    srcs = ["keymgr.c"],
    hdrs = ["keymgr.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base/freestanding",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_test(
    name = "keymgr_unittest",
    srcs = [
        "keymgr.h",
        "keymgr.c",
        "keymgr_unittest.cc"
    ],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base/freestanding",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib/base:mock_sec_mmio",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "keymgr_functest",
    srcs = ["keymgr_functest.c"],
    # FIXME: currently, the FPGA doesn't wake up from low-power mode.
    # For now, run the test only in verilator.
    targets = ["verilator"],
    deps = [
        ":keymgr",
        ":lifecycle",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "lifecycle",
    srcs = ["lifecycle.c"],
    hdrs = ["lifecycle.h"],
    deps = [
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "mock_lifecycle",
    testonly = True,
    hdrs = [
        "lifecycle.h",
        "mock_lifecycle.h",
    ],
    deps = [
      "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "lifecycle_unittest",
    srcs = [
        "lifecycle.c",
        "lifecycle.h",
        "lifecycle_unittest.cc",
    ],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:mock_sec_mmio",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = ["otbn.c"],
    hdrs = ["otbn.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "otbn_unittest",
    srcs = [
        "otbn.c",
        "otbn.h",
        "otbn_unittest.cc"
    ],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otp",
    srcs = ["otp.c"],
    hdrs = ["otp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "mock_otp",
    testonly = True,
    hdrs = [
        "mock_otp.h",
        "otp.h",
    ],
    deps = [
      "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "otp_unittest",
    srcs = [
        "otp.h",
        "otp.c",
        "otp_unittest.cc",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:mock_sec_mmio",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pinmux",
    srcs = ["pinmux.c"],
    hdrs = ["pinmux.h"],
    deps = [
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
    ],
)

cc_test(
    name = "pinmux_unittest",
    srcs = ["pinmux_unittest.cc"],
    deps = [
        ":pinmux",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "retention_sram",
    srcs = ["retention_sram.c"],
    hdrs = ["retention_sram.h"],
    deps = [
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "retention_sram_unittest",
    srcs = ["retention_sram_unittest.cc"],
    deps = [
        ":retention_sram",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "retention_sram_functest",
    srcs = ["retention_sram_functest.c"],
    deps = [
        ":retention_sram",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:test_main",
    ],
)

cc_library(
    name = "rnd",
    srcs = ["rnd.c"],
    hdrs = ["rnd.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":otp",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
    ],
)

cc_library(
    name = "mock_rnd",
    testonly = True,
    hdrs = [
        "mock_rnd.h",
        "rnd.h",
    ],
    deps = [
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

opentitan_functest(
    name = "rnd_functest",
    srcs = ["rnd_functest.c"],
    deps = [
        ":rnd",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:test_main",
    ],
)

cc_library(
    name = "rstmgr",
    srcs = ["rstmgr.c"],
    hdrs = ["rstmgr.h"],
    deps = [
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_test(
    name = "rstmgr_unittest",
    srcs = [
        "rstmgr.c",
        "rstmgr.h",
        "rstmgr_unittest.cc",
    ],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "uart",
    srcs = ["uart.c"],
    hdrs = ["uart.h"],
    deps = [
        "//hw/ip/uart/data:uart_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "uart_unittest",
    srcs = ["uart_unittest.cc"],
    deps = [
        ":uart",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "uart_functest",
    srcs = ["uart_functest.c"],
    deps = [
        ":uart",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:test_main",
    ],
)

cc_library(
    name = "watchdog",
    srcs = ["watchdog.c"],
    hdrs = ["watchdog.h"],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
    ],
)

cc_test(
    name = "watchdog_unittest",
    srcs = ["watchdog_unittest.cc"],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        ":watchdog",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing:mock_abs_mmio",
        "//sw/device/silicon_creator/lib/base:mock_sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:mock_otp",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "watchdog_functest",
    srcs = ["watchdog_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":retention_sram",
        ":rstmgr",
        ":watchdog",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)
