# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "english_breakfast_test_rom_driver_srcs",
    srcs = [
        "flash_ctrl.c",
        "flash_ctrl.h",
        "lifecycle.h",
        "otp.h",
        "rstmgr.h",
        "spi_device.c",
        "spi_device.h",
    ],
)

dual_cc_library(
    name = "alert",
    srcs = dual_inputs(
        device = ["alert.c"],
        host = ["mock_alert.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_alert.h"],
        shared = ["alert.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/top_earlgrey:alert_handler_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":lifecycle",
            ":otp",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:memory",
            "//sw/device/silicon_creator/lib:crc32",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

cc_test(
    name = "alert_unittest",
    srcs = ["alert_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":alert"),
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib:crc32",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "alert_functest",
    srcs = ["alert_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":alert",
        ":rstmgr",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "ast",
    srcs = ["ast.c"],
    hdrs = ["ast.h"],
    deps = [
        ":lifecycle",
        ":otp",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:multibits",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "ast_unittest",
    srcs = ["ast_unittest.cc"],
    deps = [
        ":ast",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "flash_ctrl",
    srcs = dual_inputs(
        device = ["flash_ctrl.c"],
        host = ["mock_flash_ctrl.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_flash_ctrl.h"],
        shared = ["flash_ctrl.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:memory",
            "//sw/device/lib/base:multibits",
            "//sw/device/silicon_creator/lib:error",
            "//sw/device/silicon_creator/lib/base:sec_mmio",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    ),
)

cc_test(
    name = "flash_ctrl_unittest",
    srcs = ["flash_ctrl_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":flash_ctrl"),
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "hmac",
    srcs = dual_inputs(
        device = ["hmac.c"],
        host = ["mock_hmac.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_hmac.h"],
        shared = ["hmac.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/ip/hmac/data:hmac_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:memory",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

cc_test(
    name = "hmac_unittest",
    srcs = ["hmac_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":hmac"),
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "hmac_functest",
    srcs = ["hmac_functest.c"],
    deps = [
        ":hmac",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_library(
    name = "ibex",
    srcs = ["ibex.c"],
    hdrs = ["ibex.h"],
    deps = [
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_test(
    name = "ibex_unittest",
    srcs = ["ibex_unittest.cc"],
    deps = [
        ":ibex",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "keymgr",
    srcs = ["keymgr.c"],
    hdrs = ["keymgr.h"],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_test(
    name = "keymgr_unittest",
    srcs = ["keymgr_unittest.cc"],
    deps = [
        ":keymgr",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "keymgr_functest",
    srcs = ["keymgr_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":keymgr",
        ":lifecycle",
        ":retention_sram",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "kmac",
    srcs = ["kmac.c"],
    hdrs = ["kmac.h"],
    deps = [
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "kmac_unittest",
    srcs = ["kmac_unittest.cc"],
    deps = [
        ":kmac",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "kmac_functest",
    srcs = ["kmac_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":kmac",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:error",
    ],
)

dual_cc_library(
    name = "lifecycle",
    srcs = dual_inputs(
        device = ["lifecycle.c"],
        host = ["mock_lifecycle.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_lifecycle.h"],
        shared = ["lifecycle.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/base:sec_mmio",
        ],
    ),
)

cc_test(
    name = "lifecycle_unittest",
    srcs = ["lifecycle_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":lifecycle"),
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = ["otbn.c"],
    hdrs = ["otbn.h"],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:rnd",
    ],
)

cc_test(
    name = "otbn_unittest",
    srcs = ["otbn_unittest.cc"],
    deps = [
        ":otbn",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "otp",
    srcs = dual_inputs(
        device = ["otp.c"],
        host = ["mock_otp.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_otp.h"],
        shared = ["otp.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/base:sec_mmio",
        ],
    ),
)

cc_test(
    name = "otp_unittest",
    srcs = ["otp_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":otp"),
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pinmux",
    srcs = ["pinmux.c"],
    hdrs = ["pinmux.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

cc_test(
    name = "pinmux_unittest",
    srcs = ["pinmux_unittest.cc"],
    deps = [
        ":pinmux",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:sim_dv",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/testing:rom_test",
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
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "retention_sram_unittest",
    srcs = ["retention_sram_unittest.cc"],
    deps = [
        ":retention_sram",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "retention_sram_functest",
    srcs = ["retention_sram_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":retention_sram",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:error",
    ],
)

dual_cc_library(
    name = "rnd",
    srcs = dual_inputs(
        device = ["rnd.c"],
        host = ["mock_rnd.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_rnd.h"],
        shared = ["rnd.h"],
    ),
    deps = dual_inputs(
        device = [
            ":otp",
            "//sw/device/lib/base:csr",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:hardened",
            "//hw/ip/entropy_src/data:entropy_src_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/silicon_creator/lib:crc32",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":lifecycle",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

cc_test(
    name = "rnd_unittest",
    srcs = ["rnd_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":rnd"),
        ":otp",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "rnd_functest",
    srcs = ["rnd_functest.c"],
    deps = [
        ":otp",
        ":rnd",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:crc32",
        "//sw/device/silicon_creator/lib:error",
    ],
)

dual_cc_library(
    name = "rstmgr",
    srcs = dual_inputs(
        device = ["rstmgr.c"],
        host = ["mock_rstmgr.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_rstmgr.h"],
        shared = ["rstmgr.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:multibits",
            "//sw/device/lib/runtime:hart",
            "//sw/device/silicon_creator/lib:error",
            "//sw/device/silicon_creator/lib/base:sec_mmio",
        ],
    ),
)

cc_test(
    name = "rstmgr_unittest",
    srcs = ["rstmgr_unittest.cc"],
    deps = [
        dual_cc_device_library_of(":rstmgr"),
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "rstmgr_functest",
    srcs = ["rstmgr_functest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
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
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "uart_unittest",
    srcs = ["uart_unittest.cc"],
    deps = [
        ":uart",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

opentitan_functest(
    name = "uart_functest",
    srcs = ["uart_functest.c"],
    deps = [
        ":uart",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:error",
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
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

cc_test(
    name = "watchdog_unittest",
    srcs = ["watchdog_unittest.cc"],
    deps = [
        ":watchdog",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/testing:rom_test",
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
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

dual_cc_library(
    name = "spi_device",
    srcs = dual_inputs(
        device = ["spi_device.c"],
        host = ["mock_spi_device.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_spi_device.h"],
        shared = ["spi_device.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/ip/spi_device/data:spi_device_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            ":lifecycle",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:memory",
            "//sw/device/silicon_creator/lib:error",
        ],
    ),
)

cc_test(
    name = "spi_device_unittest",
    srcs = [
        "spi_device_unittest.cc",
    ],
    deps = [
        dual_cc_device_library_of(":spi_device"),
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pwrmgr",
    srcs = ["pwrmgr.c"],
    hdrs = ["pwrmgr.h"],
    deps = [
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)
