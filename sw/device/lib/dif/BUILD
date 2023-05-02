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
        "//sw/device/lib/base/internal:status",
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
        "autogen/dif_adc_ctrl_autogen_unittest.cc",
        "dif_adc_ctrl_unittest.cc",
    ],
    deps = [
        ":adc_ctrl",
        ":test_base",
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
        "autogen/dif_aes_autogen_unittest.cc",
        "dif_aes_unittest.cc",
    ],
    deps = [
        ":aes",
        ":test_base",
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
        "autogen/dif_alert_handler_autogen_unittest.cc",
        "dif_alert_handler_unittest.cc",
    ],
    deps = [
        ":alert_handler",
        ":test_base",
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
        "autogen/dif_aon_timer_autogen_unittest.cc",
        "dif_aon_timer_unittest.cc",
    ],
    deps = [
        ":aon_timer",
        ":test_base",
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
        "autogen/dif_clkmgr_autogen_unittest.cc",
        "dif_clkmgr_unittest.cc",
    ],
    deps = [
        ":clkmgr",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "csrng_shared",
    srcs = [
        "autogen/dif_csrng_autogen.h",
        "dif_csrng_shared.c",
    ],
    hdrs = [
        "dif_csrng.h",
        "dif_csrng_shared.h",
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
        ":csrng_shared",
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
        "autogen/dif_csrng_autogen_unittest.cc",
        "dif_csrng_unittest.cc",
    ],
    deps = [
        ":csrng",
        ":test_base",
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
        ":csrng_shared",
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
        "autogen/dif_edn_autogen_unittest.cc",
        "dif_edn_unittest.cc",
    ],
    deps = [
        ":edn",
        ":test_base",
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
        "autogen/dif_entropy_src_autogen_unittest.cc",
        "dif_entropy_src_unittest.cc",
    ],
    deps = [
        ":entropy_src",
        ":test_base",
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
        "autogen/dif_flash_ctrl_autogen_unittest.cc",
        "dif_flash_ctrl_unittest.cc",
    ],
    deps = [
        ":flash_ctrl",
        ":test_base",
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
        "autogen/dif_gpio_autogen_unittest.cc",
        "dif_gpio_unittest.cc",
    ],
    deps = [
        ":gpio",
        ":test_base",
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
        "autogen/dif_hmac_autogen_unittest.cc",
        "dif_hmac_unittest.cc",
    ],
    deps = [
        ":hmac",
        ":test_base",
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
        "autogen/dif_i2c_autogen_unittest.cc",
        "dif_i2c_unittest.cc",
    ],
    deps = [
        ":i2c",
        ":test_base",
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
        "autogen/dif_keymgr_autogen_unittest.cc",
        "dif_keymgr_unittest.cc",
    ],
    deps = [
        ":keymgr",
        ":test_base",
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
        "autogen/dif_kmac_autogen_unittest.cc",
        "dif_kmac_unittest.cc",
    ],
    deps = [
        ":kmac",
        ":test_base",
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
        "autogen/dif_lc_ctrl_autogen_unittest.cc",
        "dif_lc_ctrl_unittest.cc",
    ],
    deps = [
        ":lc_ctrl",
        ":test_base",
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
        "autogen/dif_otbn_autogen_unittest.cc",
        "dif_otbn_unittest.cc",
    ],
    deps = [
        ":otbn",
        ":test_base",
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
        "autogen/dif_otp_ctrl_autogen_unittest.cc",
        "dif_otp_ctrl_unittest.cc",
    ],
    deps = [
        ":otp_ctrl",
        ":test_base",
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
        "autogen/dif_pattgen_autogen_unittest.cc",
        "dif_pattgen_unittest.cc",
    ],
    deps = [
        ":pattgen",
        ":test_base",
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
        "//sw/device/lib/runtime:hart",
    ],
)

cc_test(
    name = "pinmux_unittest",
    srcs = [
        "autogen/dif_pinmux_autogen_unittest.cc",
        "dif_pinmux_unittest.cc",
    ],
    deps = [
        ":pinmux",
        ":test_base",
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
        "autogen/dif_pwm_autogen_unittest.cc",
    ],
    deps = [
        ":pwm",
        ":test_base",
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
        "autogen/dif_pwrmgr_autogen_unittest.cc",
        "dif_pwrmgr_unittest.cc",
    ],
    deps = [
        ":pwrmgr",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rom_ctrl",
    srcs = [
        "autogen/dif_rom_ctrl_autogen.c",
        "autogen/dif_rom_ctrl_autogen.h",
        "dif_rom_ctrl.c",
    ],
    hdrs = [
        "dif_rom_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/ip/rom_ctrl/data:rom_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "rom_ctrl_unittest",
    srcs = [
        "autogen/dif_rom_ctrl_autogen_unittest.cc",
    ],
    deps = [
        ":rom_ctrl",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rstmgr_intf",
    srcs = ["autogen/dif_rstmgr_autogen.h"],
    hdrs = ["dif_rstmgr.h"],
    deps = [":base"],
)

cc_library(
    name = "rstmgr",
    srcs = [
        "autogen/dif_rstmgr_autogen.c",
        "dif_rstmgr.c",
    ],
    deps = [
        ":base",
        ":rstmgr_intf",
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
        "autogen/dif_rstmgr_autogen_unittest.cc",
        "dif_rstmgr_unittest.cc",
    ],
    deps = [
        ":rstmgr",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_core_ibex",
    srcs = [
        "autogen/dif_rv_core_ibex_autogen.c",
        "autogen/dif_rv_core_ibex_autogen.h",
        "dif_rv_core_ibex.c",
    ],
    hdrs = [
        "dif_rv_core_ibex.h",
    ],
    deps = [
        ":base",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/runtime:hart",
    ],
)

cc_test(
    name = "rv_core_ibex_unittest",
    srcs = [
        "autogen/dif_rv_core_ibex_autogen_unittest.cc",
        "dif_rv_core_ibex_unittest.cc",
    ],
    deps = [
        ":rv_core_ibex",
        ":test_base",
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
        "autogen/dif_rv_plic_autogen_unittest.cc",
        "dif_rv_plic_unittest.cc",
    ],
    deps = [
        ":rv_plic",
        ":test_base",
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
        "autogen/dif_rv_timer_autogen_unittest.cc",
        "dif_rv_timer_unittest.cc",
    ],
    deps = [
        ":rv_timer",
        ":test_base",
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
        "autogen/dif_spi_device_autogen_unittest.cc",
        "dif_spi_device_unittest.cc",
    ],
    deps = [
        ":spi_device",
        ":test_base",
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
        "autogen/dif_spi_host_autogen_unittest.cc",
        "dif_spi_host_unittest.cc",
    ],
    deps = [
        ":spi_host",
        ":test_base",
        "//sw/device/lib/base:global_mock",
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
        "autogen/dif_sram_ctrl_autogen_unittest.cc",
        "dif_sram_ctrl_unittest.cc",
    ],
    deps = [
        ":sram_ctrl",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sensor_ctrl",
    srcs = [
        "autogen/dif_sensor_ctrl_autogen.c",
        "autogen/dif_sensor_ctrl_autogen.h",
        "dif_sensor_ctrl.c",
    ],
    hdrs = [
        "dif_sensor_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
    ],
)

cc_test(
    name = "sensor_ctrl_unittest",
    srcs = [
        "autogen/dif_sensor_ctrl_autogen_unittest.cc",
        "dif_sensor_ctrl_unittest.cc",
    ],
    deps = [
        ":sensor_ctrl",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sysrst_ctrl",
    srcs = [
        "autogen/dif_sysrst_ctrl_autogen.c",
        "autogen/dif_sysrst_ctrl_autogen.h",
        "dif_sysrst_ctrl.c",
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
        "autogen/dif_sysrst_ctrl_autogen_unittest.cc",
        "dif_sysrst_ctrl_unittest.cc",
    ],
    deps = [
        ":sysrst_ctrl",
        ":test_base",
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
        "autogen/dif_uart_autogen_unittest.cc",
        "dif_uart_unittest.cc",
    ],
    deps = [
        ":test_base",
        ":uart",
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
        "autogen/dif_usbdev_autogen_unittest.cc",
        "dif_usbdev_unittest.cc",
    ],
    deps = [
        ":test_base",
        ":usbdev",
        "@googletest//:gtest_main",
    ],
)
