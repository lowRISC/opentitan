# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "adc_ctrl",
    srcs = [
        "//sw/ip/adc_ctrl/dif:headers",
        "//sw/ip/adc_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/adc_ctrl/dif:api",
    ],
    deps = [
        "//hw/ip/adc_ctrl/data:adc_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "adc_ctrl_unittest",
    srcs = [
        "//sw/ip/adc_ctrl/dif:test_sources",
    ],
    deps = [
        ":adc_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "aes",
    srcs = [
        "//sw/ip/aes/dif:headers",
        "//sw/ip/aes/dif:sources",
    ],
    hdrs = [
        "//sw/ip/aes/dif:api",
    ],
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "aes_unittest",
    srcs = [
        "//sw/ip/aes/dif:test_sources",
    ],
    deps = [
        ":aes",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "alert_handler",
    srcs = [
        "//sw/ip/alert_handler/dif:headers",
        "//sw/ip/alert_handler/dif:sources",
    ],
    hdrs = [
        "//sw/ip/alert_handler/dif:api",
    ],
    deps = [
        "//hw/top_darjeeling:alert_handler_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "alert_handler_unittest",
    srcs = [
        "//sw/ip/alert_handler/dif:test_sources",
    ],
    deps = [
        ":alert_handler",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "aon_timer",
    srcs = [
        "//sw/ip/aon_timer/dif:headers",
        "//sw/ip/aon_timer/dif:sources",
    ],
    hdrs = [
        "//sw/ip/aon_timer/dif:api",
    ],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "aon_timer_unittest",
    srcs = [
        "//sw/ip/aon_timer/dif:test_sources",
    ],
    deps = [
        ":aon_timer",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "clkmgr",
    srcs = [
        "//sw/ip/clkmgr/dif:headers",
        "//sw/ip/clkmgr/dif:sources",
    ],
    hdrs = [
        "//sw/ip/clkmgr/dif:api",
    ],
    deps = [
        "//hw/top_darjeeling/ip/clkmgr/data/autogen:clkmgr_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "clkmgr_unittest",
    srcs = [
        "//sw/ip/clkmgr/dif:test_sources",
    ],
    deps = [
        ":clkmgr",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "csrng_shared",
    srcs = [
        "//sw/ip/csrng/dif:headers",
        "//sw/ip/csrng/dif:shared_headers",
        "//sw/ip/csrng/dif:shared_sources",
    ],
    hdrs = [
        "//sw/ip/csrng/dif:api",
        "//sw/ip/csrng/dif:shared_api",
    ],
    deps = [
        "//hw/ip/csrng/data:csrng_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_library(
    name = "csrng",
    srcs = [
        "//sw/ip/csrng/dif:headers",
        "//sw/ip/csrng/dif:sources",
    ],
    hdrs = [
        "//sw/ip/csrng/dif:api",
    ],
    deps = [
        ":csrng_shared",
        "//hw/ip/csrng/data:csrng_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "csrng_unittest",
    srcs = [
        "//sw/ip/csrng/dif:test_sources",
    ],
    deps = [
        ":csrng",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "dma",
    srcs = [
        "//sw/ip/dma/dif:headers",
        "//sw/ip/dma/dif:sources",
    ],
    hdrs = [
        "//sw/ip/dma/dif:api",
    ],
    deps = [
        "//hw/ip/dma/data:dma_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "dma_unittest",
    srcs = [
        "//sw/ip/dma/dif:test_sources",
    ],
    deps = [
        ":dma",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "edn",
    srcs = [
        "//sw/ip/edn/dif:headers",
        "//sw/ip/edn/dif:sources",
    ],
    hdrs = [
        "//sw/ip/edn/dif:api",
    ],
    deps = [
        ":csrng_shared",
        "//hw/ip/edn/data:edn_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "edn_unittest",
    srcs = [
        "//sw/ip/edn/dif:test_sources",
    ],
    deps = [
        ":edn",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "entropy_src",
    srcs = [
        "//sw/ip/entropy_src/dif:headers",
        "//sw/ip/entropy_src/dif:sources",
    ],
    hdrs = [
        "//sw/ip/entropy_src/dif:api",
    ],
    deps = [
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "entropy_src_unittest",
    srcs = [
        "//sw/ip/entropy_src/dif:test_sources",
    ],
    deps = [
        ":entropy_src",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "flash_ctrl",
    srcs = [
        "//sw/ip/flash_ctrl/dif:headers",
        "//sw/ip/flash_ctrl/dif:sources",
    ],
    deps = [
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "flash_ctrl_unittest",
    srcs = [
        "//sw/ip/flash_ctrl/dif:test_sources",
    ],
    deps = [
        ":flash_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "gpio",
    srcs = [
        "//sw/ip/gpio/dif:headers",
        "//sw/ip/gpio/dif:sources",
    ],
    hdrs = [
        "//sw/ip/gpio/dif:api",
    ],
    deps = [
        "//hw/ip/gpio/data:gpio_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "gpio_unittest",
    srcs = [
        "//sw/ip/gpio/dif:test_sources",
    ],
    deps = [
        ":gpio",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "hmac",
    srcs = [
        "//sw/ip/hmac/dif:headers",
        "//sw/ip/hmac/dif:sources",
    ],
    hdrs = [
        "//sw/ip/hmac/dif:api",
    ],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "hmac_unittest",
    srcs = [
        "//sw/ip/hmac/dif:test_sources",
    ],
    deps = [
        ":hmac",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "i2c",
    srcs = [
        "//sw/ip/i2c/dif:headers",
        "//sw/ip/i2c/dif:sources",
    ],
    hdrs = [
        "//sw/ip/i2c/dif:api",
    ],
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "i2c_unittest",
    srcs = [
        "//sw/ip/i2c/dif:test_sources",
    ],
    deps = [
        ":i2c",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "keymgr",
    srcs = [
        "//sw/ip/keymgr/dif:headers",
        "//sw/ip/keymgr/dif:sources",
    ],
    hdrs = [
        "//sw/ip/keymgr/dif:api",
    ],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "keymgr_unittest",
    srcs = [
        "//sw/ip/keymgr/dif:test_sources",
    ],
    deps = [
        ":keymgr",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "keymgr_dpe",
    srcs = [
        "//sw/ip/keymgr_dpe/dif:headers",
        "//sw/ip/keymgr_dpe/dif:sources",
    ],
    hdrs = [
        "//sw/ip/keymgr_dpe/dif:api",
    ],
    deps = [
        "//hw/ip/keymgr_dpe/data:keymgr_dpe_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "keymgr_dpe_unittest",
    srcs = [
        "//sw/ip/keymgr_dpe/dif:test_sources",
    ],
    deps = [
        ":keymgr_dpe",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "kmac",
    srcs = [
        "//sw/ip/kmac/dif:headers",
        "//sw/ip/kmac/dif:sources",
    ],
    hdrs = [
        "//sw/ip/kmac/dif:api",
    ],
    deps = [
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "kmac_unittest",
    srcs = [
        "//sw/ip/kmac/dif:test_sources",
    ],
    deps = [
        ":kmac",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "lc_ctrl",
    srcs = [
        "//sw/ip/lc_ctrl/dif:headers",
        "//sw/ip/lc_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/lc_ctrl/dif:api",
    ],
    deps = [
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "lc_ctrl_unittest",
    srcs = [
        "//sw/ip/lc_ctrl/dif:test_sources",
    ],
    deps = [
        ":lc_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "mbx",
    srcs = [
        "//sw/ip/mbx/dif:headers",
        "//sw/ip/mbx/dif:sources",
    ],
    hdrs = [
        "//sw/ip/mbx/dif:api",
    ],
    deps = [
        "//hw/ip/mbx/data:mbx_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_test(
    name = "mbx_unittest",
    srcs = [
        "//sw/ip/mbx/dif:test_sources",
    ],
    deps = [
        ":mbx",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = [
        "//sw/ip/otbn/dif:headers",
        "//sw/ip/otbn/dif:sources",
    ],
    hdrs = [
        "//sw/ip/otbn/dif:api",
    ],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "otbn_unittest",
    srcs = [
        "//sw/ip/otbn/dif:test_sources",
    ],
    deps = [
        ":otbn",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otp_ctrl",
    srcs = [
        "//sw/ip/otp_ctrl/dif:headers",
        "//sw/ip/otp_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/otp_ctrl/dif:api",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "otp_ctrl_unittest",
    srcs = [
        "//sw/ip/otp_ctrl/dif:test_sources",
    ],
    deps = [
        ":otp_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pattgen",
    srcs = [
        "//sw/ip/pattgen/dif:headers",
        "//sw/ip/pattgen/dif:sources",
    ],
    hdrs = [
        "//sw/ip/pattgen/dif:api",
    ],
    deps = [
        "//hw/ip/pattgen/data:pattgen_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "pattgen_unittest",
    srcs = [
        "//sw/ip/pattgen/dif:test_sources",
    ],
    deps = [
        ":pattgen",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pinmux",
    srcs = [
        "//sw/ip/pinmux/dif:headers",
        "//sw/ip/pinmux/dif:sources",
    ],
    hdrs = [
        "//sw/ip/pinmux/dif:api",
    ],
    deps = [
        "//hw/top_darjeeling/ip/pinmux/data/autogen:pinmux_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/runtime:hart",
    ],
)

cc_test(
    name = "pinmux_unittest",
    srcs = [
        "//sw/ip/pinmux/dif:test_sources",
    ],
    deps = [
        ":pinmux",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pwm",
    srcs = [
        "//sw/ip/pwm/dif:headers",
        "//sw/ip/pwm/dif:sources",
    ],
    hdrs = [
        "//sw/ip/pwm/dif:api",
    ],
    deps = [
        "//hw/ip/pwm/data:pwm_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "pwm_unittest",
    srcs = [
        "//sw/ip/pwm/dif:test_sources",
    ],
    deps = [
        ":pwm",
        "//sw/ip/base/dif:test_base",
        "//sw/lib/sw/device/base:global_mock",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pwrmgr",
    srcs = [
        "//sw/ip/pwrmgr/dif:headers",
        "//sw/ip/pwrmgr/dif:sources",
    ],
    hdrs = [
        "//sw/ip/pwrmgr/dif:api",
    ],
    deps = [
        "//hw/top_darjeeling/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "pwrmgr_unittest",
    srcs = [
        "//sw/ip/pwrmgr/dif:test_sources",
    ],
    deps = [
        ":pwrmgr",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rom_ctrl",
    srcs = [
        "//sw/ip/rom_ctrl/dif:headers",
        "//sw/ip/rom_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/rom_ctrl/dif:api",
    ],
    deps = [
        "//hw/ip/rom_ctrl/data:rom_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "rom_ctrl_unittest",
    srcs = [
        "//sw/ip/rom_ctrl/dif:test_sources",
    ],
    deps = [
        ":rom_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rstmgr_intf",
    srcs = [
        "//sw/ip/rstmgr/dif:headers",
    ],
    hdrs = [
        "//sw/ip/rstmgr/dif:api",
    ],
    linkstatic = True,
    deps = [
        "//sw/ip/base/dif:base",
    ],
)

cc_library(
    name = "rstmgr",
    srcs = [
        "//sw/ip/rstmgr/dif:sources",
    ],
    deps = [
        ":rstmgr_intf",
        "//hw/top_darjeeling/ip/rstmgr/data/autogen:rstmgr_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "rstmgr_unittest",
    srcs = [
        "//sw/ip/rstmgr/dif:test_sources",
    ],
    deps = [
        ":rstmgr",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_core_ibex",
    srcs = [
        "//sw/ip/rv_core_ibex/dif:headers",
        "//sw/ip/rv_core_ibex/dif:sources",
    ],
    hdrs = [
        "//sw/ip/rv_core_ibex/dif:api",
    ],
    deps = [
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
    ],
)

cc_test(
    name = "rv_core_ibex_unittest",
    srcs = [
        "//sw/ip/rv_core_ibex/dif:test_sources",
    ],
    deps = [
        ":rv_core_ibex",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_plic",
    srcs = [
        "//sw/ip/rv_plic/dif:headers",
        "//sw/ip/rv_plic/dif:sources",
    ],
    hdrs = [
        "//sw/ip/rv_plic/dif:headers",
    ],
    deps = [
        "//hw/top_darjeeling:rv_plic_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "rv_plic_unittest",
    srcs = [
        "//sw/ip/rv_plic/dif:test_sources",
    ],
    deps = [
        ":rv_plic",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_timer",
    srcs = [
        "//sw/ip/rv_timer/dif:headers",
        "//sw/ip/rv_timer/dif:sources",
    ],
    hdrs = [
        "//sw/ip/rv_timer/dif:api",
    ],
    deps = [
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "rv_timer_unittest",
    srcs = [
        "//sw/ip/rv_timer/dif:test_sources",
    ],
    deps = [
        ":rv_timer",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "spi_device",
    srcs = [
        "//sw/ip/spi_device/dif:headers",
        "//sw/ip/spi_device/dif:sources",
    ],
    hdrs = [
        "//sw/ip/spi_device/dif:api",
    ],
    deps = [
        "//hw/ip/spi_device/data:spi_device_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "spi_device_unittest",
    srcs = [
        "//sw/ip/spi_device/dif:test_sources",
    ],
    deps = [
        ":spi_device",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "spi_host",
    srcs = [
        "//sw/ip/spi_host/dif:headers",
        "//sw/ip/spi_host/dif:sources",
    ],
    hdrs = [
        "//sw/ip/spi_host/dif:api",
    ],
    deps = [
        "//hw/ip/spi_host/data:spi_host_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "spi_host_unittest",
    srcs = [
        "//sw/ip/spi_host/dif:test_sources",
    ],
    deps = [
        ":spi_host",
        "//sw/ip/base/dif:test_base",
        "//sw/lib/sw/device/base:global_mock",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sram_ctrl",
    srcs = [
        "//sw/ip/sram_ctrl/dif:headers",
        "//sw/ip/sram_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/sram_ctrl/dif:api",
    ],
    deps = [
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "sram_ctrl_unittest",
    srcs = [
        "//sw/ip/sram_ctrl/dif:test_sources",
    ],
    deps = [
        ":sram_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sensor_ctrl",
    srcs = [
        "//sw/ip/sensor_ctrl/dif:headers",
        "//sw/ip/sensor_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/sensor_ctrl/dif:api",
    ],
    deps = [
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_test(
    name = "sensor_ctrl_unittest",
    srcs = [
        "//sw/ip/sensor_ctrl/dif:test_sources",
    ],
    deps = [
        ":sensor_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "soc_proxy",
    srcs = [
        "//sw/ip/soc_proxy/dif:headers",
        "//sw/ip/soc_proxy/dif:sources",
    ],
    hdrs = [
        "//sw/ip/soc_proxy/dif:api",
    ],
    deps = [
        "//hw/top_darjeeling/ip/soc_proxy/data:soc_proxy_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_test(
    name = "soc_proxy_unittest",
    srcs = [
        "//sw/ip/soc_proxy/dif:test_sources",
    ],
    deps = [
        ":soc_proxy",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sysrst_ctrl",
    srcs = [
        "//sw/ip/sysrst_ctrl/dif:headers",
        "//sw/ip/sysrst_ctrl/dif:sources",
    ],
    hdrs = [
        "//sw/ip/sysrst_ctrl/dif:headers",
    ],
    deps = [
        "//hw/ip/sysrst_ctrl/data:sysrst_ctrl_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "sysrst_ctrl_unittest",
    srcs = [
        "//sw/ip/sysrst_ctrl/dif:test_sources",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "uart",
    srcs = [
        "//sw/ip/uart/dif:headers",
        "//sw/ip/uart/dif:sources",
    ],
    hdrs = [
        "//sw/ip/uart/dif:api",
    ],
    deps = [
        "//hw/ip/uart/data:uart_regs",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/base:multibits",
    ],
)

cc_test(
    name = "uart_unittest",
    srcs = [
        "//sw/ip/uart/dif:test_sources",
    ],
    deps = [
        ":uart",
        "//sw/ip/base/dif:test_base",
        "@googletest//:gtest_main",
    ],
)
