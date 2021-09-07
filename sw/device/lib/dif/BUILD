# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
    hdrs = [
        "dif_base.h",
    ],
)

cc_library(
    name = "clkmgr",
    srcs = [
        "dif_clkmgr.c",
    ],
    hdrs = ["dif_clkmgr.h"],
    deps = [
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "clkmgr_unittest",
    srcs = [
        "dif_clkmgr.c",
        "dif_clkmgr.h",
        "dif_clkmgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "csrng",
    srcs = [
        "dif_csrng.c",
    ],
    hdrs = [
        "dif_csrng.h",
    ],
    deps = [
        "//hw/ip/csrng/data:csrng_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "csrng_unittest",
    srcs = [
        "dif_csrng.c",
        "dif_csrng.h",
        "dif_csrng_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/csrng/data:csrng_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "edn",
    srcs = [
        "dif_edn.c",
    ],
    hdrs = [
        "dif_edn.h",
    ],
    deps = [
        "//hw/ip/edn/data:edn_regs",
        "//sw/device/lib/base",
    ],
)

cc_library(
    name = "uart",
    srcs = [
        "autogen/dif_uart_autogen.c",
        "autogen/dif_uart_autogen.inc",
        "dif_uart.c",
    ],
    hdrs = ["dif_uart.h"],
    deps = [
        "base",
        "//hw/ip/uart/data:uart_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "uart_unittest",
    srcs = [
        "autogen/dif_uart_autogen.inc",
        "dif_uart.c",
        "dif_uart.h",
        "dif_uart_unittest.cc",
        "dif_uart_unittest.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "base",
        "//hw/ip/uart/data:uart_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_plic",
    srcs = [
        "dif_rv_plic.c",
    ],
    hdrs = [
        "dif_rv_plic.h",
    ],
    deps = [
        "//hw/top_earlgrey/ip/rv_plic/data/autogen:rv_plic_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "rv_plic_unittest",
    srcs = [
        "dif_rv_plic.c",
        "dif_rv_plic.h",
        "dif_rv_plic_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/top_earlgrey/ip/rv_plic/data/autogen:rv_plic_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "gpio",
    srcs = [
        "dif_gpio.c",
    ],
    hdrs = [
        "dif_gpio.h",
    ],
    deps = [
        "//hw/ip/gpio/data:gpio_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "gpio_unittest",
    srcs = [
        "dif_gpio.c",
        "dif_gpio.h",
        "dif_gpio_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/gpio/data:gpio_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "spi_device",
    srcs = [
        "dif_spi_device.c",
    ],
    hdrs = [
        "dif_spi_device.h",
    ],
    deps = [
        "//hw/ip/spi_device/data:spi_device_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "spi_device_unittest",
    srcs = [
        "dif_spi_device.c",
        "dif_spi_device.h",
        "dif_spi_device_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/spi_device/data:spi_device_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_timer",
    srcs = [
        "dif_rv_timer.c",
    ],
    hdrs = [
        "dif_rv_timer.h",
    ],
    deps = [
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "rv_timer_unittest",
    srcs = [
        "dif_rv_timer.c",
        "dif_rv_timer.h",
        "dif_rv_timer_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "i2c",
    srcs = [
        "dif_i2c.c",
    ],
    hdrs = [
        "dif_i2c.h",
    ],
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "i2c_unittest",
    srcs = [
        "dif_i2c.c",
        "dif_i2c.h",
        "dif_i2c_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "usbdev",
    srcs = [
        "dif_usbdev.c",
    ],
    hdrs = [
        "dif_usbdev.h",
    ],
    deps = [
        "//hw/ip/usbdev/data:usbdev_regs",
        "//sw/device/lib/base",
    ],
)

cc_library(
    name = "hmac",
    srcs = [
        "dif_hmac.c",
    ],
    hdrs = [
        "dif_hmac.h",
    ],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//sw/device/lib/base",
    ],
)

cc_library(
    name = "kmac",
    srcs = [
        "dif_kmac.c",
    ],
    hdrs = [
        "dif_kmac.h",
    ],
    deps = [
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "kmac_unittest",
    srcs = [
        "dif_kmac.c",
        "dif_kmac.h",
        "dif_kmac_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = [
        "dif_otbn.c",
    ],
    hdrs = [
        "dif_otbn.h",
    ],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "otbn_unittest",
    srcs = [
        "dif_otbn.c",
        "dif_otbn.h",
        "dif_otbn_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rstmgr",
    srcs = [
        "dif_rstmgr.c",
    ],
    hdrs = [
        "dif_rstmgr.h",
    ],
    deps = [
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "rstmgr_unittest",
    srcs = [
        "dif_rstmgr.c",
        "dif_rstmgr.h",
        "dif_rstmgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "alert_handler",
    srcs = [
        "dif_alert_handler.c",
    ],
    hdrs = [
        "dif_alert_handler.h",
    ],
    deps = [
        "//hw/top_earlgrey/ip/alert_handler/data/autogen:alert_handler_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "alert_handler_unittest",
    srcs = [
        "dif_alert_handler.c",
        "dif_alert_handler.h",
        "dif_alert_handler_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/top_earlgrey/ip/alert_handler/data/autogen:alert_handler_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pwrmgr",
    srcs = [
        "dif_pwrmgr.c",
    ],
    hdrs = [
        "dif_pwrmgr.h",
    ],
    deps = [
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "pwrmgr_unittest",
    srcs = [
        "dif_pwrmgr.c",
        "dif_pwrmgr.h",
        "dif_pwrmgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "keymgr",
    srcs = [
        "dif_keymgr.c",
    ],
    hdrs = [
        "dif_keymgr.h",
    ],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "keymgr_unittest",
    srcs = [
        "dif_keymgr.c",
        "dif_keymgr.h",
        "dif_keymgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otp_ctrl",
    srcs = [
        "dif_otp_ctrl.c",
    ],
    hdrs = [
        "dif_otp_ctrl.h",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "otp_ctrl_unittest",
    srcs = [
        "dif_otp_ctrl.c",
        "dif_otp_ctrl.h",
        "dif_otp_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "lc_ctrl",
    srcs = [
        "dif_lc_ctrl.c",
    ],
    hdrs = [
        "dif_lc_ctrl.h",
    ],
    deps = [
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "lc_ctrl_unittest",
    srcs = [
        "dif_lc_ctrl.c",
        "dif_lc_ctrl.h",
        "dif_lc_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "aon_timer",
    srcs = [
        "dif_aon_timer.c",
    ],
    hdrs = [
        "dif_aon_timer.h",
    ],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "aon_timer_unittest",
    srcs = [
        "dif_aon_timer.c",
        "dif_aon_timer.h",
        "dif_aon_timer_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "entropy_src",
    srcs = [
        "dif_entropy_src.c",
    ],
    hdrs = [
        "dif_entropy_src.h",
    ],
    deps = [
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "entropy_src_unittest",
    srcs = [
        "dif_entropy_src.c",
        "dif_entropy_src.h",
        "dif_entropy_src_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "aes",
    srcs = [
        "dif_aes.c",
    ],
    hdrs = [
        "dif_aes.h",
    ],
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//sw/device/lib/base",
    ],
)

cc_test(
    name = "aes_unittest",
    srcs = [
        "dif_aes.c",
        "dif_aes.h",
        "dif_aes_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//sw/device/lib/base",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pinmux",
    srcs = [
        "dif_pinmux.c",
    ],
    hdrs = [
        "dif_pinmux.h",
    ],
    deps = [
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//sw/device/lib/base",
    ],
)

cc_library(
    name = "sram_ctrl",
    srcs = [
        "dif_sram_ctrl.c",
    ],
    hdrs = [
        "dif_sram_ctrl.h",
    ],
    deps = [
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//sw/device/lib/base",
    ],
)
