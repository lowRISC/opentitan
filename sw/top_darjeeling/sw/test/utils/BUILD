# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "isr_testutils",
    srcs = ["autogen/isr_testutils.c"],
    hdrs = ["autogen/isr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:dma",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:keymgr_dpe",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:mbx",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/dif:soc_proxy",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/dif:sysrst_ctrl",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

cc_library(
    name = "aes_testutils",
    srcs = ["//sw/ip/aes/test/utils:aes_testutils.c"],
    hdrs = ["//sw/ip/aes/test/utils:aes_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":csrng_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:csrng_shared",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/drivers:csrng",
        "//sw/top_darjeeling/sw/drivers:edn",
    ],
)

cc_library(
    name = "alert_handler_testutils",
    srcs = ["//sw/ip/alert_handler/test/utils:alert_handler_testutils.c"],
    hdrs = ["//sw/ip/alert_handler/test/utils:alert_handler_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:rstmgr",
    ],
)

cc_library(
    name = "aon_timer_testutils",
    srcs = ["//sw/ip/aon_timer/test/utils:aon_timer_testutils.c"],
    hdrs = ["//sw/ip/aon_timer/test/utils:aon_timer_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:math",
        "//sw/top_darjeeling/sw/dif:aon_timer",
    ],
)

cc_library(
    name = "clkmgr_testutils",
    srcs = ["//sw/ip/clkmgr/test/utils:clkmgr_testutils.c"],
    hdrs = ["//sw/ip/clkmgr/test/utils:clkmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_darjeeling/sw/dif:clkmgr",
    ],
)

cc_library(
    name = "csrng_testutils",
    srcs = ["//sw/ip/csrng/test/utils:csrng_testutils.c"],
    hdrs = ["//sw/ip/csrng/test/utils:csrng_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_darjeeling/sw/dif:csrng",
    ],
)

cc_library(
    name = "entropy_testutils",
    srcs = ["//sw/ip/entropy_src/test/utils:entropy_testutils.c"],
    hdrs = ["//sw/ip/entropy_src/test/utils:entropy_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/edn/data:edn_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:mmio",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:csrng_shared",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:entropy_src",
        "//sw/top_darjeeling/sw/drivers:csrng",
        "//sw/top_darjeeling/sw/drivers:edn",
        "//sw/top_darjeeling/sw/drivers:entropy_src",
    ],
)

cc_library(
    name = "flash_ctrl_testutils",
    srcs = ["//sw/ip/flash_ctrl/test/utils:flash_ctrl_testutils.c"],
    hdrs = ["//sw/ip/flash_ctrl/test/utils:flash_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/drivers:flash_ctrl",
    ],
)

cc_library(
    name = "nv_counter_testutils",
    srcs = ["//sw/ip/flash_ctrl/test/utils:nv_counter_testutils.c"],
    hdrs = ["//sw/ip/flash_ctrl/test/utils:nv_counter_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":flash_ctrl_testutils",
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
    ],
)

cc_library(
    name = "hmac_testutils",
    srcs = ["//sw/ip/hmac/test/utils:hmac_testutils.c"],
    hdrs = ["//sw/ip/hmac/test/utils:hmac_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_darjeeling/sw/dif:hmac",
    ],
)

cc_library(
    name = "i2c_testutils",
    srcs = [
        "i2c_testutils_pinmux.c",
        "//sw/ip/i2c/test/utils:i2c_testutils.c",
    ],
    hdrs = ["//sw/ip/i2c/test/utils:i2c_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:pinmux",
    ],
)

cc_library(
    name = "keymgr_dpe_testutils",
    srcs = ["//sw/ip/keymgr_dpe/test/utils:keymgr_dpe_testutils.c"],
    hdrs = ["//sw/ip/keymgr_dpe/test/utils:keymgr_dpe_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":flash_ctrl_testutils",
        ":kmac_testutils",
        ":otp_ctrl_testutils",
        ":rstmgr_testutils",
        "//hw/ip/keymgr_dpe/data:keymgr_dpe_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:keymgr_dpe",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/drivers:keymgr_dpe",
        "//sw/top_darjeeling/sw/drivers:kmac",
        "//sw/top_darjeeling/sw/drivers:otp_ctrl",
        "//sw/top_darjeeling/sw/drivers:rstmgr",
    ],
)

cc_library(
    name = "keymgr_testutils",
    srcs = ["//sw/ip/keymgr/test/utils:keymgr_testutils.c"],
    hdrs = ["//sw/ip/keymgr/test/utils:keymgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":flash_ctrl_testutils",
        ":kmac_testutils",
        ":otp_ctrl_testutils",
        ":rstmgr_testutils",
        "//hw/ip/keymgr/data:keymgr_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:keymgr",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/drivers:keymgr",
        "//sw/top_darjeeling/sw/drivers:kmac",
        "//sw/top_darjeeling/sw/drivers:otp_ctrl",
        "//sw/top_darjeeling/sw/drivers:rstmgr",
    ],
)

cc_library(
    name = "kmac_testutils",
    srcs = ["//sw/ip/kmac/test/utils:kmac_testutils.c"],
    hdrs = ["//sw/ip/kmac/test/utils:kmac_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_darjeeling/sw/dif:kmac",
    ],
)

cc_library(
    name = "lc_ctrl_testutils",
    srcs = ["//sw/ip/lc_ctrl/test/utils:lc_ctrl_testutils.c"],
    hdrs = ["//sw/ip/lc_ctrl/test/utils:lc_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:lc_ctrl",
    ],
)

cc_library(
    name = "otbn_testutils",
    srcs = ["//sw/ip/otbn/test/utils:otbn_testutils.c"],
    hdrs = ["//sw/ip/otbn/test/utils:otbn_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:otbn",
    ],
)

cc_library(
    name = "otp_ctrl_testutils",
    srcs = ["//sw/ip/otp_ctrl/test/utils:otp_ctrl_testutils.c"],
    hdrs = ["//sw/ip/otp_ctrl/test/utils:otp_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
    ],
)

cc_library(
    name = "pinmux_testutils",
    srcs = ["pinmux_testutils.c"],
    hdrs = ["//sw/ip/pinmux/test/utils:pinmux_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:pinmux",
    ],
)

cc_library(
    name = "pwrmgr_testutils",
    srcs = ["//sw/ip/pwrmgr/test/utils:pwrmgr_testutils.c"],
    hdrs = ["//sw/ip/pwrmgr/test/utils:pwrmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
    ],
)

cc_library(
    name = "rand_testutils",
    srcs = ["//sw/ip/rv_core_ibex/test/utils:rand_testutils.c"],
    hdrs = ["//sw/ip/rv_core_ibex/test/utils:rand_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
    ],
)

cc_library(
    name = "rstmgr_testutils",
    srcs = ["//sw/ip/rstmgr/test/utils:rstmgr_testutils.c"],
    hdrs = ["//sw/ip/rstmgr/test/utils:rstmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/top_darjeeling/sw/dif:rstmgr",
    ],
)

cc_library(
    name = "rv_core_ibex_testutils",
    srcs = ["//sw/ip/rv_core_ibex/test/utils:rv_core_ibex_testutils.c"],
    hdrs = ["//sw/ip/rv_core_ibex/test/utils:rv_core_ibex_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
    ],
)

cc_library(
    name = "rv_plic_testutils",
    srcs = ["//sw/ip/rv_plic/test/utils:rv_plic_testutils.c"],
    hdrs = ["//sw/ip/rv_plic/test/utils:rv_plic_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:rv_plic",
    ],
)

cc_library(
    name = "sensor_ctrl_testutils",
    srcs = ["//sw/ip/sensor_ctrl/test/utils:sensor_ctrl_testutils.c"],
    hdrs = ["//sw/ip/sensor_ctrl/test/utils:sensor_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
    ],
)

cc_library(
    name = "sram_ctrl_testutils",
    srcs = ["//sw/ip/sram_ctrl/test/utils:sram_ctrl_testutils.c"],
    hdrs = ["//sw/ip/sram_ctrl/test/utils:sram_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/dif:sram_ctrl",
    ],
)

cc_library(
    name = "ret_sram_testutils",
    srcs = ["//sw/ip/sram_ctrl/test/utils:ret_sram_testutils.c"],
    hdrs = ["//sw/ip/sram_ctrl/test/utils:ret_sram_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/lib/sw/device/base:status",
    ],
)

cc_library(
    name = "spi_device_testutils",
    srcs = ["//sw/ip/spi_device/test/utils:spi_device_testutils.c"],
    hdrs = ["//sw/ip/spi_device/test/utils:spi_device_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/json:spi_passthru",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:status",
        "//sw/top_darjeeling/sw/dif:spi_device",
    ],
)

cc_library(
    name = "spi_host_testutils",
    srcs = ["//sw/ip/spi_host/test/utils:spi_host_testutils.c"],
    hdrs = ["//sw/ip/spi_host/test/utils:spi_host_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:status",
        "//sw/top_darjeeling/sw/dif:spi_host",
    ],
)

cc_library(
    name = "spi_flash_testutils",
    srcs = [
        "//sw/ip/spi_host/test/utils:spi_flash_emulator.c",
        "//sw/ip/spi_host/test/utils:spi_flash_testutils.c",
    ],
    hdrs = [
        "//sw/ip/spi_host/test/utils:spi_flash_emulator.h",
        "//sw/ip/spi_host/test/utils:spi_flash_testutils.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":spi_device_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:status",
        "//sw/top_darjeeling/sw/dif:spi_host",
    ],
)
