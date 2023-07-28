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
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:adc_ctrl",
        "//sw/top_earlgrey/sw/dif:alert_handler",
        "//sw/top_earlgrey/sw/dif:aon_timer",
        "//sw/top_earlgrey/sw/dif:csrng",
        "//sw/top_earlgrey/sw/dif:dma",
        "//sw/top_earlgrey/sw/dif:edn",
        "//sw/top_earlgrey/sw/dif:entropy_src",
        "//sw/top_earlgrey/sw/dif:flash_ctrl",
        "//sw/top_earlgrey/sw/dif:gpio",
        "//sw/top_earlgrey/sw/dif:hmac",
        "//sw/top_earlgrey/sw/dif:i2c",
        "//sw/top_earlgrey/sw/dif:keymgr",
        "//sw/top_earlgrey/sw/dif:kmac",
        "//sw/top_earlgrey/sw/dif:otbn",
        "//sw/top_earlgrey/sw/dif:otp_ctrl",
        "//sw/top_earlgrey/sw/dif:pattgen",
        "//sw/top_earlgrey/sw/dif:pwrmgr",
        "//sw/top_earlgrey/sw/dif:rv_plic",
        "//sw/top_earlgrey/sw/dif:rv_timer",
        "//sw/top_earlgrey/sw/dif:sensor_ctrl",
        "//sw/top_earlgrey/sw/dif:spi_device",
        "//sw/top_earlgrey/sw/dif:spi_host",
        "//sw/top_earlgrey/sw/dif:sysrst_ctrl",
        "//sw/top_earlgrey/sw/dif:uart",
        "//sw/top_earlgrey/sw/dif:usbdev",
    ],
)

cc_library(
    name = "aes_testutils",
    srcs = ["aes_testutils.c"],
    hdrs = ["aes_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_earlgrey/sw/dif:aes",
        "//sw/top_earlgrey/sw/dif:csrng_shared",
        "//sw/top_earlgrey/sw/dif:edn",
    ],
)

cc_library(
    name = "alert_handler_testutils",
    srcs = ["alert_handler_testutils.c"],
    hdrs = ["alert_handler_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/top_earlgrey/sw/dif:alert_handler",
        "//sw/top_earlgrey/sw/dif:rstmgr",
    ],
)

cc_library(
    name = "aon_timer_testutils",
    srcs = ["aon_timer_testutils.c"],
    hdrs = ["aon_timer_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:math",
        "//sw/top_earlgrey/sw/dif:aon_timer",
    ],
)

cc_library(
    name = "clkmgr_testutils",
    srcs = ["clkmgr_testutils.c"],
    hdrs = ["clkmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_earlgrey/sw/dif:clkmgr",
    ],
)

cc_library(
    name = "csrng_testutils",
    srcs = ["csrng_testutils.c"],
    hdrs = ["csrng_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:csrng",
    ],
)

cc_library(
    name = "entropy_testutils",
    srcs = ["entropy_testutils.c"],
    hdrs = ["entropy_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/edn/data:edn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:mmio",
        "//sw/top_earlgrey/sw/dif:csrng",
        "//sw/top_earlgrey/sw/dif:csrng_shared",
        "//sw/top_earlgrey/sw/dif:edn",
        "//sw/top_earlgrey/sw/dif:entropy_src",
    ],
)

cc_library(
    name = "flash_ctrl_testutils",
    srcs = ["flash_ctrl_testutils.c"],
    hdrs = ["flash_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_earlgrey/sw/dif:flash_ctrl",
    ],
)

cc_library(
    name = "nv_counter_testutils",
    srcs = ["nv_counter_testutils.c"],
    hdrs = ["nv_counter_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":flash_ctrl_testutils",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:flash_ctrl",
    ],
)

cc_library(
    name = "hmac_testutils",
    srcs = ["hmac_testutils.c"],
    hdrs = ["hmac_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_earlgrey/sw/dif:hmac",
    ],
)

cc_library(
    name = "i2c_testutils",
    srcs = ["i2c_testutils.c"],
    hdrs = ["i2c_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_earlgrey/sw/dif:i2c",
        "//sw/top_earlgrey/sw/dif:pinmux",
    ],
)

cc_library(
    name = "keymgr_testutils",
    srcs = ["keymgr_testutils.c"],
    hdrs = ["keymgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_earlgrey/sw/dif:flash_ctrl",
        "//sw/top_earlgrey/sw/dif:keymgr",
        "//sw/top_earlgrey/sw/dif:otp_ctrl",
        "//sw/top_earlgrey/sw/dif:rstmgr",
    ],
)

cc_library(
    name = "kmac_testutils",
    srcs = ["kmac_testutils.c"],
    hdrs = ["kmac_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:kmac",
    ],
)

cc_library(
    name = "lc_ctrl_testutils",
    srcs = ["lc_ctrl_testutils.c"],
    hdrs = ["lc_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/dif:lc_ctrl",
    ],
)

cc_library(
    name = "otbn_testutils",
    srcs = ["otbn_testutils.c"],
    hdrs = ["otbn_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/dif:otbn",
    ],
)

cc_library(
    name = "otp_ctrl_testutils",
    srcs = ["otp_ctrl_testutils.c"],
    hdrs = ["otp_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/dif:otp_ctrl",
    ],
)

cc_library(
    name = "pinmux_testutils",
    srcs = ["pinmux_testutils.c"],
    hdrs = ["pinmux_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_earlgrey/sw/dif:gpio",
        "//sw/top_earlgrey/sw/dif:pinmux",
    ],
)

cc_library(
    name = "profile",
    srcs = ["profile.c"],
    hdrs = ["profile.h"],
    deps = [
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

cc_library(
    name = "pwrmgr_testutils",
    srcs = ["pwrmgr_testutils.c"],
    hdrs = ["pwrmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:pwrmgr",
    ],
)

cc_library(
    name = "rand_testutils",
    srcs = ["rand_testutils.c"],
    hdrs = ["rand_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rv_core_ibex_testutils",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/dif:rv_core_ibex",
    ],
)

cc_library(
    name = "rstmgr_testutils",
    srcs = ["rstmgr_testutils.c"],
    hdrs = ["rstmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/top_earlgrey/sw/dif:rstmgr",
    ],
)

cc_library(
    name = "rv_core_ibex_testutils",
    srcs = ["rv_core_ibex_testutils.c"],
    hdrs = ["rv_core_ibex_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/top_earlgrey/sw/dif:rv_core_ibex",
    ],
)

cc_library(
    name = "rv_plic_testutils",
    srcs = ["rv_plic_testutils.c"],
    hdrs = ["rv_plic_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/dif:rv_plic",
    ],
)

cc_library(
    name = "sensor_ctrl_testutils",
    srcs = ["sensor_ctrl_testutils.c"],
    hdrs = ["sensor_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/top_earlgrey/sw/dif:sensor_ctrl",
    ],
)

cc_library(
    name = "sram_ctrl_testutils",
    srcs = ["sram_ctrl_testutils.c"],
    hdrs = ["sram_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_earlgrey/sw/dif:sram_ctrl",
    ],
)

cc_library(
    name = "spi_device_testutils",
    srcs = ["spi_device_testutils.c"],
    hdrs = ["spi_device_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/json:spi_passthru",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:status",
        "//sw/top_earlgrey/sw/dif:spi_device",
    ],
)

cc_library(
    name = "spi_host_testutils",
    srcs = ["spi_host_testutils.c"],
    hdrs = ["spi_host_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:status",
        "//sw/top_earlgrey/sw/dif:spi_host",
    ],
)

cc_library(
    name = "spi_flash_testutils",
    srcs = [
        "spi_flash_emulator.c",
        "spi_flash_testutils.c",
    ],
    hdrs = [
        "spi_flash_emulator.h",
        "spi_flash_testutils.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":spi_device_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:status",
        "//sw/top_earlgrey/sw/dif:spi_host",
    ],
)

cc_library(
    name = "usb_testutils",
    srcs = [
        "usb_testutils.c",
        "usb_testutils_controlep.c",
    ],
    hdrs = [
        "usb_testutils.h",
        "usb_testutils_controlep.h",
        "usb_testutils_diags.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/top_earlgrey/sw/dif:usbdev",
    ],
)

cc_library(
    name = "usb_testutils_simpleserial",
    srcs = ["usb_testutils_simpleserial.c"],
    hdrs = ["usb_testutils_simpleserial.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":usb_testutils",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

cc_library(
    name = "usb_testutils_streams",
    srcs = ["usb_testutils_streams.c"],
    hdrs = ["usb_testutils_streams.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":usb_testutils",
        "//sw/device/lib/testing/test_framework:check",
    ],
)
