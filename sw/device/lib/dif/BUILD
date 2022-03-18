# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
    srcs = ["dif_base.c"],
    hdrs = ["dif_base.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
    ],
)

cc_library(
    name = "test_base",
    testonly = True,
    hdrs = ["dif_test_base.h"],
    deps = [
        ":base",
        "@googletest//:gtest",
    ],
)

cc_library(
    name = "adc_ctrl",
    srcs = [
        "autogen/dif_adc_ctrl_autogen.c",
        "autogen/dif_adc_ctrl_autogen.h",
        "dif_adc_ctrl.c",
    ],
    hdrs = [
        "dif_adc_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/adc_ctrl/data:adc_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "adc_ctrl_unittest",
    srcs = [
        "autogen/dif_adc_ctrl_autogen.c",
        "autogen/dif_adc_ctrl_autogen.h",
        "autogen/dif_adc_ctrl_autogen_unittest.cc",
        "dif_adc_ctrl.c",
        "dif_adc_ctrl.h",
        "dif_adc_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/adc_ctrl/data:adc_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "clkmgr",
    srcs = [
        "autogen/dif_clkmgr_autogen.c",
        "autogen/dif_clkmgr_autogen.h",
        "dif_clkmgr.c",
    ],
    hdrs = ["dif_clkmgr.h"],
    deps = [
        ":base",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "clkmgr_unittest",
    srcs = [
        "autogen/dif_clkmgr_autogen.c",
        "autogen/dif_clkmgr_autogen.h",
        "autogen/dif_clkmgr_autogen_unittest.cc",
        "dif_clkmgr.c",
        "dif_clkmgr.h",
        "dif_clkmgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "csrng",
    srcs = [
        "autogen/dif_csrng_autogen.c",
        "autogen/dif_csrng_autogen.h",
        "dif_csrng.c",
    ],
    hdrs = [
        "dif_csrng.h",
    ],
    deps = [
        ":base",
        "//hw/ip/csrng/data:csrng_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "csrng_unittest",
    srcs = [
        "autogen/dif_csrng_autogen.c",
        "autogen/dif_csrng_autogen.h",
        "autogen/dif_csrng_autogen_unittest.cc",
        "dif_csrng.c",
        "dif_csrng.h",
        "dif_csrng_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/csrng/data:csrng_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "edn",
    srcs = [
        "autogen/dif_edn_autogen.c",
        "autogen/dif_edn_autogen.h",
        "dif_edn.c",
    ],
    hdrs = [
        "dif_edn.h",
    ],
    deps = [
        ":base",
        "//hw/ip/edn/data:edn_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "edn_unittest",
    srcs = [
        "autogen/dif_edn_autogen.c",
        "autogen/dif_edn_autogen.h",
        "autogen/dif_edn_autogen_unittest.cc",
        "dif_edn.c",
        "dif_edn.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/edn/data:edn_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "uart",
    srcs = [
        "autogen/dif_uart_autogen.c",
        "autogen/dif_uart_autogen.h",
        "dif_uart.c",
    ],
    hdrs = ["dif_uart.h"],
    deps = [
        ":base",
        "//hw/ip/uart/data:uart_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "uart_unittest",
    srcs = [
        "autogen/dif_uart_autogen.c",
        "autogen/dif_uart_autogen.h",
        "autogen/dif_uart_autogen_unittest.cc",
        "dif_uart.c",
        "dif_uart.h",
        "dif_uart_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/uart/data:uart_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_plic",
    srcs = [
        "autogen/dif_rv_plic_autogen.c",
        "autogen/dif_rv_plic_autogen.h",
        "dif_rv_plic.c",
    ],
    hdrs = [
        "dif_rv_plic.h",
    ],
    deps = [
        ":base",
        "//hw/top_earlgrey:rv_plic_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "rv_plic_unittest",
    srcs = [
        "autogen/dif_rv_plic_autogen.c",
        "autogen/dif_rv_plic_autogen.h",
        "autogen/dif_rv_plic_autogen_unittest.cc",
        "dif_rv_plic.c",
        "dif_rv_plic.h",
        "dif_rv_plic_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/top_earlgrey:rv_plic_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "gpio",
    srcs = [
        "autogen/dif_gpio_autogen.c",
        "autogen/dif_gpio_autogen.h",
        "dif_gpio.c",
    ],
    hdrs = [
        "dif_gpio.h",
    ],
    deps = [
        ":base",
        "//hw/ip/gpio/data:gpio_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "gpio_unittest",
    srcs = [
        "autogen/dif_gpio_autogen.c",
        "autogen/dif_gpio_autogen.h",
        "autogen/dif_gpio_autogen_unittest.cc",
        "dif_gpio.c",
        "dif_gpio.h",
        "dif_gpio_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/gpio/data:gpio_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "spi_device",
    srcs = [
        "autogen/dif_spi_device_autogen.c",
        "autogen/dif_spi_device_autogen.h",
        "dif_spi_device.c",
    ],
    hdrs = [
        "dif_spi_device.h",
    ],
    deps = [
        ":base",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "spi_device_unittest",
    srcs = [
        "autogen/dif_spi_device_autogen.c",
        "autogen/dif_spi_device_autogen.h",
        "autogen/dif_spi_device_autogen_unittest.cc",
        "dif_spi_device.c",
        "dif_spi_device.h",
        "dif_spi_device_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "spi_host",
    srcs = [
        "autogen/dif_spi_host_autogen.c",
        "autogen/dif_spi_host_autogen.h",
        "dif_spi_host.c",
    ],
    hdrs = [
        "dif_spi_host.h",
    ],
    deps = [
        ":base",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "spi_host_unittest",
    srcs = [
        "autogen/dif_spi_host_autogen.c",
        "autogen/dif_spi_host_autogen.h",
        "autogen/dif_spi_host_autogen_unittest.cc",
        "dif_spi_host.c",
        "dif_spi_host.h",
        "dif_spi_host_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "//sw/device/lib/base/testing:global_mock",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_timer",
    srcs = [
        "autogen/dif_rv_timer_autogen.c",
        "autogen/dif_rv_timer_autogen.h",
        "dif_rv_timer.c",
    ],
    hdrs = [
        "dif_rv_timer.h",
    ],
    deps = [
        ":base",
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "rv_timer_unittest",
    srcs = [
        "autogen/dif_rv_timer_autogen.c",
        "autogen/dif_rv_timer_autogen.h",
        "autogen/dif_rv_timer_autogen_unittest.cc",
        "dif_rv_timer.c",
        "dif_rv_timer.h",
        "dif_rv_timer_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "i2c",
    srcs = [
        "autogen/dif_i2c_autogen.c",
        "autogen/dif_i2c_autogen.h",
        "dif_i2c.c",
    ],
    hdrs = [
        "dif_i2c.h",
    ],
    deps = [
        ":base",
        "//hw/ip/i2c/data:i2c_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "i2c_unittest",
    srcs = [
        "autogen/dif_i2c_autogen.c",
        "autogen/dif_i2c_autogen.h",
        "autogen/dif_i2c_autogen_unittest.cc",
        "dif_i2c.c",
        "dif_i2c.h",
        "dif_i2c_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/i2c/data:i2c_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "usbdev",
    srcs = [
        "autogen/dif_usbdev_autogen.c",
        "autogen/dif_usbdev_autogen.h",
        "dif_usbdev.c",
    ],
    hdrs = [
        "dif_usbdev.h",
    ],
    deps = [
        ":base",
        "//hw/ip/usbdev/data:usbdev_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "usbdev_unittest",
    srcs = [
        "autogen/dif_usbdev_autogen.c",
        "autogen/dif_usbdev_autogen.h",
        "autogen/dif_usbdev_autogen_unittest.cc",
        "dif_usbdev.c",
        "dif_usbdev.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/usbdev/data:usbdev_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "hmac",
    srcs = [
        "autogen/dif_hmac_autogen.c",
        "autogen/dif_hmac_autogen.h",
        "dif_hmac.c",
    ],
    hdrs = [
        "dif_hmac.h",
    ],
    deps = [
        ":base",
        "//hw/ip/hmac/data:hmac_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "hmac_unittest",
    srcs = [
        "autogen/dif_hmac_autogen.c",
        "autogen/dif_hmac_autogen.h",
        "autogen/dif_hmac_autogen_unittest.cc",
        "dif_hmac.c",
        "dif_hmac.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/hmac/data:hmac_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "kmac",
    srcs = [
        "autogen/dif_kmac_autogen.c",
        "autogen/dif_kmac_autogen.h",
        "dif_kmac.c",
    ],
    hdrs = [
        "dif_kmac.h",
    ],
    deps = [
        ":base",
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "kmac_unittest",
    srcs = [
        "autogen/dif_kmac_autogen.c",
        "autogen/dif_kmac_autogen.h",
        "autogen/dif_kmac_autogen_unittest.cc",
        "dif_kmac.c",
        "dif_kmac.h",
        "dif_kmac_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = [
        "autogen/dif_otbn_autogen.c",
        "autogen/dif_otbn_autogen.h",
        "dif_otbn.c",
    ],
    hdrs = [
        "dif_otbn.h",
    ],
    deps = [
        ":base",
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "otbn_unittest",
    srcs = [
        "autogen/dif_otbn_autogen.c",
        "autogen/dif_otbn_autogen.h",
        "autogen/dif_otbn_autogen_unittest.cc",
        "dif_otbn.c",
        "dif_otbn.h",
        "dif_otbn_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rstmgr",
    srcs = [
        "autogen/dif_rstmgr_autogen.c",
        "autogen/dif_rstmgr_autogen.h",
        "dif_rstmgr.c",
    ],
    hdrs = [
        "dif_rstmgr.h",
    ],
    deps = [
        ":base",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "rstmgr_unittest",
    srcs = [
        "autogen/dif_rstmgr_autogen.c",
        "autogen/dif_rstmgr_autogen.h",
        "autogen/dif_rstmgr_autogen_unittest.cc",
        "dif_rstmgr.c",
        "dif_rstmgr.h",
        "dif_rstmgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "alert_handler",
    srcs = [
        "autogen/dif_alert_handler_autogen.c",
        "autogen/dif_alert_handler_autogen.h",
        "dif_alert_handler.c",
    ],
    hdrs = [
        "dif_alert_handler.h",
    ],
    deps = [
        ":base",
        "//hw/top_earlgrey:alert_handler_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "alert_handler_unittest",
    srcs = [
        "autogen/dif_alert_handler_autogen.c",
        "autogen/dif_alert_handler_autogen.h",
        "autogen/dif_alert_handler_autogen_unittest.cc",
        "dif_alert_handler.c",
        "dif_alert_handler.h",
        "dif_alert_handler_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/top_earlgrey:alert_handler_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pwrmgr",
    srcs = [
        "autogen/dif_pwrmgr_autogen.c",
        "autogen/dif_pwrmgr_autogen.h",
        "dif_pwrmgr.c",
    ],
    hdrs = [
        "dif_pwrmgr.h",
    ],
    deps = [
        ":base",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "pwrmgr_unittest",
    srcs = [
        "autogen/dif_pwrmgr_autogen.c",
        "autogen/dif_pwrmgr_autogen.h",
        "autogen/dif_pwrmgr_autogen_unittest.cc",
        "dif_pwrmgr.c",
        "dif_pwrmgr.h",
        "dif_pwrmgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "keymgr",
    srcs = [
        "autogen/dif_keymgr_autogen.c",
        "autogen/dif_keymgr_autogen.h",
        "dif_keymgr.c",
    ],
    hdrs = [
        "dif_keymgr.h",
    ],
    deps = [
        ":base",
        "//hw/ip/keymgr/data:keymgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "keymgr_unittest",
    srcs = [
        "autogen/dif_keymgr_autogen.c",
        "autogen/dif_keymgr_autogen.h",
        "autogen/dif_keymgr_autogen_unittest.cc",
        "dif_keymgr.c",
        "dif_keymgr.h",
        "dif_keymgr_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/keymgr/data:keymgr_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otp_ctrl",
    srcs = [
        "autogen/dif_otp_ctrl_autogen.c",
        "autogen/dif_otp_ctrl_autogen.h",
        "dif_otp_ctrl.c",
    ],
    hdrs = [
        "dif_otp_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "otp_ctrl_unittest",
    srcs = [
        "autogen/dif_otp_ctrl_autogen.c",
        "autogen/dif_otp_ctrl_autogen.h",
        "autogen/dif_otp_ctrl_autogen_unittest.cc",
        "dif_otp_ctrl.c",
        "dif_otp_ctrl.h",
        "dif_otp_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pattgen",
    srcs = [
        "autogen/dif_pattgen_autogen.c",
        "autogen/dif_pattgen_autogen.h",
        "dif_pattgen.c",
    ],
    hdrs = [
        "dif_pattgen.h",
    ],
    deps = [
        ":base",
        "//hw/ip/pattgen/data:pattgen_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "pattgen_unittest",
    srcs = [
        "autogen/dif_pattgen_autogen.c",
        "autogen/dif_pattgen_autogen.h",
        "autogen/dif_pattgen_autogen_unittest.cc",
        "dif_pattgen.c",
        "dif_pattgen.h",
        "dif_pattgen_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/pattgen/data:pattgen_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "lc_ctrl",
    srcs = [
        "autogen/dif_lc_ctrl_autogen.c",
        "autogen/dif_lc_ctrl_autogen.h",
        "dif_lc_ctrl.c",
    ],
    hdrs = [
        "dif_lc_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "lc_ctrl_unittest",
    srcs = [
        "autogen/dif_lc_ctrl_autogen.c",
        "autogen/dif_lc_ctrl_autogen.h",
        "autogen/dif_lc_ctrl_autogen_unittest.cc",
        "dif_lc_ctrl.c",
        "dif_lc_ctrl.h",
        "dif_lc_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "aon_timer",
    srcs = [
        "autogen/dif_aon_timer_autogen.c",
        "autogen/dif_aon_timer_autogen.h",
        "dif_aon_timer.c",
    ],
    hdrs = [
        "dif_aon_timer.h",
    ],
    deps = [
        ":base",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "aon_timer_unittest",
    srcs = [
        "autogen/dif_aon_timer_autogen.c",
        "autogen/dif_aon_timer_autogen.h",
        "autogen/dif_aon_timer_autogen_unittest.cc",
        "dif_aon_timer.c",
        "dif_aon_timer.h",
        "dif_aon_timer_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "entropy_src",
    srcs = [
        "autogen/dif_entropy_src_autogen.c",
        "autogen/dif_entropy_src_autogen.h",
        "dif_entropy_src.c",
    ],
    hdrs = [
        "dif_entropy_src.h",
    ],
    deps = [
        ":base",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "entropy_src_unittest",
    srcs = [
        "autogen/dif_entropy_src_autogen.c",
        "autogen/dif_entropy_src_autogen.h",
        "autogen/dif_entropy_src_autogen_unittest.cc",
        "dif_entropy_src.c",
        "dif_entropy_src.h",
        "dif_entropy_src_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "flash_ctrl",
    srcs = [
        "autogen/dif_flash_ctrl_autogen.c",
        "autogen/dif_flash_ctrl_autogen.h",
        "dif_flash_ctrl.c",
        "dif_flash_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "flash_ctrl_unittest",
    srcs = [
        "autogen/dif_flash_ctrl_autogen.c",
        "autogen/dif_flash_ctrl_autogen.h",
        "autogen/dif_flash_ctrl_autogen_unittest.cc",
        "dif_flash_ctrl.c",
        "dif_flash_ctrl.h",
        "dif_flash_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "aes",
    srcs = [
        "autogen/dif_aes_autogen.c",
        "autogen/dif_aes_autogen.h",
        "dif_aes.c",
    ],
    hdrs = [
        "dif_aes.h",
    ],
    deps = [
        ":base",
        "//hw/ip/aes/data:aes_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "aes_unittest",
    srcs = [
        "autogen/dif_aes_autogen.c",
        "autogen/dif_aes_autogen.h",
        "autogen/dif_aes_autogen_unittest.cc",
        "dif_aes.c",
        "dif_aes.h",
        "dif_aes_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/aes/data:aes_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pinmux",
    srcs = [
        "autogen/dif_pinmux_autogen.c",
        "autogen/dif_pinmux_autogen.h",
        "dif_pinmux.c",
    ],
    hdrs = [
        "dif_pinmux.h",
    ],
    deps = [
        ":base",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "pinmux_unittest",
    srcs = [
        "autogen/dif_pinmux_autogen.c",
        "autogen/dif_pinmux_autogen.h",
        "autogen/dif_pinmux_autogen_unittest.cc",
        "dif_pinmux.c",
        "dif_pinmux.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/pinmux/data:pinmux_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "pwm",
    srcs = [
        "autogen/dif_pwm_autogen.c",
        "autogen/dif_pwm_autogen.h",
        "dif_pwm.c",
    ],
    hdrs = [
        "dif_pwm.h",
    ],
    deps = [
        ":base",
        "//hw/ip/pwm/data:pwm_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "pwm_unittest",
    srcs = [
        "autogen/dif_pwm_autogen.c",
        "autogen/dif_pwm_autogen.h",
        "autogen/dif_pwm_autogen_unittest.cc",
        "dif_pwm.c",
        "dif_pwm.h",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/pwm/data:pwm_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sram_ctrl",
    srcs = [
        "autogen/dif_sram_ctrl_autogen.c",
        "autogen/dif_sram_ctrl_autogen.h",
        "dif_sram_ctrl.c",
    ],
    hdrs = [
        "dif_sram_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "sram_ctrl_unittest",
    srcs = [
        "autogen/dif_sram_ctrl_autogen.c",
        "autogen/dif_sram_ctrl_autogen.h",
        "autogen/dif_sram_ctrl_autogen_unittest.cc",
        "dif_sram_ctrl.c",
        "dif_sram_ctrl.h",
        "dif_sram_ctrl_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sysrst_ctrl",
    srcs = [
        "autogen/dif_sysrst_ctrl_autogen.c",
        "autogen/dif_sysrst_ctrl_autogen.h",
    ],
    hdrs = [
        "dif_sysrst_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/sysrst_ctrl/data:sysrst_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "sysrst_ctrl_unittest",
    srcs = [
        "autogen/dif_sysrst_ctrl_autogen.c",
        "autogen/dif_sysrst_ctrl_autogen.h",
        "autogen/dif_sysrst_ctrl_autogen_unittest.cc",
    ],
    defines = [
        "MOCK_MMIO=1",
    ],
    deps = [
        ":base",
        ":test_base",
        "//hw/ip/sysrst_ctrl/data:sysrst_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/testing",
        "@googletest//:gtest_main",
    ],
)
