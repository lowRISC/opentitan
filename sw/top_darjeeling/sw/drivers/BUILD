# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

#cc_library(
#    name = "aes_testutils",
#    srcs = ["//sw/ip/aes/test/utils:aes_testutils.c"],
#    hdrs = ["//sw/ip/aes/test/utils:aes_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        ":csrng_testutils",
#        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#        "//sw/lib/sw/device/runtime:ibex",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:aes",
#        "//sw/top_darjeeling/sw/dif:csrng_shared",
#        "//sw/top_darjeeling/sw/dif:edn",
#    ],
#)
#
#cc_library(
#    name = "alert_handler_testutils",
#    srcs = ["//sw/ip/alert_handler/test/utils:alert_handler_testutils.c"],
#    hdrs = ["//sw/ip/alert_handler/test/utils:alert_handler_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/ip/base/dif:base",
#        "//sw/top_darjeeling/sw/dif:alert_handler",
#        "//sw/top_darjeeling/sw/dif:rstmgr",
#    ],
#)
#
#cc_library(
#    name = "aon_timer_testutils",
#    srcs = ["//sw/ip/aon_timer/test/utils:aon_timer_testutils.c"],
#    hdrs = ["//sw/ip/aon_timer/test/utils:aon_timer_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#        "//sw/lib/sw/device/arch:device",
#        "//sw/lib/sw/device/base:math",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:aon_timer",
#    ],
#)
#
#cc_library(
#    name = "clkmgr_testutils",
#    srcs = ["//sw/ip/clkmgr/test/utils:clkmgr_testutils.c"],
#    hdrs = ["//sw/ip/clkmgr/test/utils:clkmgr_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/lib/sw/device/runtime:ibex",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:clkmgr",
#    ],
#)

cc_library(
    name = "csrng",
    hdrs = ["//sw/ip/csrng/driver:csrng.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "edn",
    hdrs = ["//sw/ip/edn/driver:edn.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "entropy_src",
    hdrs = ["//sw/ip/entropy_src/driver:entropy_src.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "flash_ctrl",
    hdrs = ["//sw/ip/flash_ctrl/driver:flash_ctrl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

#cc_library(
#    name = "nv_counter_testutils",
#    srcs = ["//sw/ip/flash_ctrl/test/utils:nv_counter_testutils.c"],
#    hdrs = ["//sw/ip/flash_ctrl/test/utils:nv_counter_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        ":flash_ctrl_testutils",
#        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
#        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:flash_ctrl",
#    ],
#)
#
#cc_library(
#    name = "hmac_testutils",
#    srcs = ["//sw/ip/hmac/test/utils:hmac_testutils.c"],
#    hdrs = ["//sw/ip/hmac/test/utils:hmac_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//hw/ip/hmac/data:hmac_regs",
#        "//sw/lib/sw/device/base:mmio",
#        "//sw/lib/sw/device/runtime:ibex",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:hmac",
#    ],
#)
#
#cc_library(
#    name = "i2c_testutils",
#    srcs = ["//sw/ip/i2c/test/utils:i2c_testutils.c"],
#    hdrs = ["//sw/ip/i2c/test/utils:i2c_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//hw/ip/i2c/data:i2c_regs",
#        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#        "//sw/lib/sw/device/runtime:ibex",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:i2c",
#        "//sw/top_darjeeling/sw/dif:pinmux",
#    ],
#)

cc_library(
    name = "keymgr",
    hdrs = ["//sw/ip/keymgr/driver:keymgr.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "keymgr_dpe",
    hdrs = ["//sw/ip/keymgr_dpe/driver:keymgr_dpe.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "kmac",
    hdrs = ["//sw/ip/kmac/driver:kmac.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "lc_ctrl",
    hdrs = ["//sw/ip/lc_ctrl/driver:lc_ctrl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

#cc_library(
#    name = "otbn_testutils",
#    srcs = ["//sw/ip/otbn/test/utils:otbn_testutils.c"],
#    hdrs = ["//sw/ip/otbn/test/utils:otbn_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/lib/sw/device/runtime:ibex",
#        "//sw/lib/sw/device/runtime:log",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:otbn",
#    ],
#)

cc_library(
    name = "otp_ctrl",
    hdrs = ["//sw/ip/otp_ctrl/driver:otp_ctrl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "pinmux",
    hdrs = ["//sw/ip/pinmux/driver:pinmux.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

#cc_library(
#    name = "pwrmgr_testutils",
#    srcs = ["//sw/ip/pwrmgr/test/utils:pwrmgr_testutils.c"],
#    hdrs = ["//sw/ip/pwrmgr/test/utils:pwrmgr_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:pwrmgr",
#    ],
#)
#
#cc_library(
#    name = "rand_testutils",
#    srcs = ["//sw/ip/rv_core_ibex/test/utils:rand_testutils.c"],
#    hdrs = ["//sw/ip/rv_core_ibex/test/utils:rand_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        ":rv_core_ibex_testutils",
#        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#        "//sw/lib/sw/device/arch:device",
#        "//sw/lib/sw/device/base:memory",
#        "//sw/lib/sw/device/runtime:log",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
#    ],
#)

cc_library(
    name = "rstmgr",
    hdrs = ["//sw/ip/rstmgr/driver:rstmgr.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "rv_core_ibex",
    hdrs = ["//sw/ip/rv_core_ibex/driver:rv_core_ibex.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

#cc_library(
#    name = "rv_plic_testutils",
#    srcs = ["//sw/ip/rv_plic/test/utils:rv_plic_testutils.c"],
#    hdrs = ["//sw/ip/rv_plic/test/utils:rv_plic_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        ":rand_testutils",
#        "//sw/lib/sw/device/runtime:log",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/ip/base/dif:base",
#        "//sw/top_darjeeling/sw/dif:rv_plic",
#    ],
#)
#
#cc_library(
#    name = "sensor_ctrl_testutils",
#    srcs = ["//sw/ip/sensor_ctrl/test/utils:sensor_ctrl_testutils.c"],
#    hdrs = ["//sw/ip/sensor_ctrl/test/utils:sensor_ctrl_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/ip/base/dif:base",
#        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
#    ],
#)

cc_library(
    name = "sram_ctrl",
    hdrs = ["//sw/ip/sram_ctrl/driver:sram_ctrl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)

#cc_library(
#    name = "spi_device_testutils",
#    srcs = ["//sw/ip/spi_device/test/utils:spi_device_testutils.c"],
#    hdrs = ["//sw/ip/spi_device/test/utils:spi_device_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/lib/sw/device/base:status",
#        "//sw/device/lib/testing/json:spi_passthru",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:spi_device",
#    ],
#)
#
#cc_library(
#    name = "spi_host_testutils",
#    srcs = ["//sw/ip/spi_host/test/utils:spi_host_testutils.c"],
#    hdrs = ["//sw/ip/spi_host/test/utils:spi_host_testutils.h"],
#    target_compatible_with = [OPENTITAN_CPU],
#    deps = [
#        "//sw/lib/sw/device/base:status",
#        "//sw/device/lib/testing/test_framework:check",
#        "//sw/top_darjeeling/sw/dif:spi_host",
#    ],
#)

cc_library(
    name = "uart",
    hdrs = ["//sw/ip/uart/driver:uart.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:mmio",
    ],
)
