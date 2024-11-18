# Copyright lowRISC contributors (OpenTitan project).
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
        "dif_adc_ctrl.c",
        "//sw/device/lib/dif/autogen:adc_ctrl_hdr",
        "//sw/device/lib/dif/autogen:adc_ctrl_src",
    ],
    hdrs = [
        "dif_adc_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:adc_ctrl_c_regs",
        "//hw/top:dt_adc_ctrl",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/runtime:hart",
    ],
)

cc_test(
    name = "adc_ctrl_unittest",
    srcs = [
        "dif_adc_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:adc_ctrl_unittest",
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
        "dif_aes.c",
        "//sw/device/lib/dif/autogen:aes_hdr",
        "//sw/device/lib/dif/autogen:aes_src",
    ],
    hdrs = [
        "dif_aes.h",
    ],
    deps = [
        ":base",
        "//hw/top:aes_c_regs",
        "//hw/top:dt_aes",
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
        "dif_aes_unittest.cc",
        "//sw/device/lib/dif/autogen:aes_unittest",
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
        "dif_alert_handler.c",
        "//sw/device/lib/dif/autogen:alert_handler_hdr",
        "//sw/device/lib/dif/autogen:alert_handler_src",
    ],
    hdrs = [
        "dif_alert_handler.h",
    ],
    deps = [
        ":base",
        "//hw/top:alert_handler_c_regs",
        "//hw/top:dt_alert_handler",
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
        "dif_alert_handler_unittest.cc",
        "//sw/device/lib/dif/autogen:alert_handler_unittest",
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
        "dif_aon_timer.c",
        "//sw/device/lib/dif/autogen:aon_timer_hdr",
        "//sw/device/lib/dif/autogen:aon_timer_src",
    ],
    hdrs = [
        "dif_aon_timer.h",
    ],
    deps = [
        ":base",
        "//hw/top:aon_timer_c_regs",
        "//hw/top:dt_aon_timer",
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
        "dif_aon_timer_unittest.cc",
        "//sw/device/lib/dif/autogen:aon_timer_unittest",
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
        "dif_clkmgr.c",
        "//sw/device/lib/dif/autogen:clkmgr_hdr",
        "//sw/device/lib/dif/autogen:clkmgr_src",
    ],
    hdrs = ["dif_clkmgr.h"],
    deps = [
        ":base",
        "//hw/top:clkmgr_c_regs",
        "//hw/top:dt_clkmgr",
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
        "dif_clkmgr_unittest.cc",
        "//sw/device/lib/dif/autogen:clkmgr_unittest",
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
        "dif_csrng_shared.c",
        "//sw/device/lib/dif/autogen:csrng_hdr",
    ],
    hdrs = [
        "dif_csrng.h",
        "dif_csrng_shared.h",
    ],
    deps = [
        ":base",
        "//hw/top:csrng_c_regs",
        "//hw/top:dt_csrng",
        "//hw/top:edn_c_regs",
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
        "dif_csrng.c",
        "//sw/device/lib/dif/autogen:csrng_hdr",
        "//sw/device/lib/dif/autogen:csrng_src",
    ],
    hdrs = [
        "dif_csrng.h",
    ],
    deps = [
        ":base",
        ":csrng_shared",
        "//hw/top:csrng_c_regs",
        "//hw/top:dt_csrng",
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
        "dif_csrng_unittest.cc",
        "//sw/device/lib/dif/autogen:csrng_unittest",
    ],
    deps = [
        ":csrng",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "dma",
    srcs = [
        "dif_dma.c",
        "//sw/device/lib/dif/autogen:dma_hdr",
        "//sw/device/lib/dif/autogen:dma_src",
    ],
    hdrs = [
        "dif_dma.h",
    ],
    # TODO Update when we have a top with a keymgr_dpe.
    target_compatible_with = ["@platforms//:incompatible"],
    deps = [
        ":base",
        "//hw/top:dma_c_regs",
        "//hw/top:dt_dma",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "dma_unittest",
    srcs = [
        "dif_dma_unittest.cc",
        "//sw/device/lib/dif/autogen:dma_unittest",
    ],
    deps = [
        ":dma",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "edn",
    srcs = [
        "dif_edn.c",
        "//sw/device/lib/dif/autogen:edn_hdr",
        "//sw/device/lib/dif/autogen:edn_src",
    ],
    hdrs = [
        "dif_edn.h",
    ],
    deps = [
        ":base",
        ":csrng_shared",
        "//hw/top:dt_edn",
        "//hw/top:edn_c_regs",
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
        "dif_edn_unittest.cc",
        "//sw/device/lib/dif/autogen:edn_unittest",
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
        "dif_entropy_src.c",
        "//sw/device/lib/dif/autogen:entropy_src_hdr",
        "//sw/device/lib/dif/autogen:entropy_src_src",
    ],
    hdrs = [
        "dif_entropy_src.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_entropy_src",
        "//hw/top:entropy_src_c_regs",
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
        "dif_entropy_src_unittest.cc",
        "//sw/device/lib/dif/autogen:entropy_src_unittest",
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
        "dif_flash_ctrl.c",
        "dif_flash_ctrl.h",
        "//sw/device/lib/dif/autogen:flash_ctrl_hdr",
        "//sw/device/lib/dif/autogen:flash_ctrl_src",
    ],
    deps = [
        ":base",
        "//hw/top:dt_flash_ctrl",
        "//hw/top:flash_ctrl_c_regs",
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
        "dif_flash_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:flash_ctrl_unittest",
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
        "dif_gpio.c",
        "//sw/device/lib/dif/autogen:gpio_hdr",
        "//sw/device/lib/dif/autogen:gpio_src",
    ],
    hdrs = [
        "dif_gpio.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_gpio",
        "//hw/top:gpio_c_regs",
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
        "dif_gpio_unittest.cc",
        "//sw/device/lib/dif/autogen:gpio_unittest",
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
        "dif_hmac.c",
        "//sw/device/lib/dif/autogen:hmac_hdr",
        "//sw/device/lib/dif/autogen:hmac_src",
    ],
    hdrs = [
        "dif_hmac.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_hmac",
        "//hw/top:hmac_c_regs",
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
        "dif_hmac_unittest.cc",
        "//sw/device/lib/dif/autogen:hmac_unittest",
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
        "dif_i2c.c",
        "//sw/device/lib/dif/autogen:i2c_hdr",
        "//sw/device/lib/dif/autogen:i2c_src",
    ],
    hdrs = [
        "dif_i2c.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_i2c",
        "//hw/top:i2c_c_regs",
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
        "dif_i2c_unittest.cc",
        "//sw/device/lib/dif/autogen:i2c_unittest",
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
        "dif_keymgr.c",
        "//sw/device/lib/dif/autogen:keymgr_hdr",
        "//sw/device/lib/dif/autogen:keymgr_src",
    ],
    hdrs = [
        "dif_keymgr.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_keymgr",
        "//hw/top:keymgr_c_regs",
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
        "dif_keymgr_unittest.cc",
        "//sw/device/lib/dif/autogen:keymgr_unittest",
    ],
    deps = [
        ":keymgr",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "keymgr_dpe",
    srcs = [
        "dif_keymgr_dpe.c",
        "//sw/device/lib/dif/autogen:keymgr_dpe_hdr",
        "//sw/device/lib/dif/autogen:keymgr_dpe_src",
    ],
    hdrs = [
        "dif_keymgr_dpe.h",
    ],
    # TODO Update when we have a top with a keymgr_dpe.
    target_compatible_with = ["@platforms//:incompatible"],
    deps = [
        ":base",
        "//hw/top:dt_keymgr_dpe",
        "//hw/top:keymgr_dpe_c_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "keymgr_dpe_unittest",
    srcs = [
        "//sw/device/lib/dif/autogen:keymgr_dpe_unittest",
    ],
    deps = [
        ":keymgr_dpe",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "kmac",
    srcs = [
        "dif_kmac.c",
        "//sw/device/lib/dif/autogen:kmac_hdr",
        "//sw/device/lib/dif/autogen:kmac_src",
    ],
    hdrs = [
        "dif_kmac.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_kmac",
        "//hw/top:kmac_c_regs",
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
        "dif_kmac_unittest.cc",
        "//sw/device/lib/dif/autogen:kmac_unittest",
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
        "dif_lc_ctrl.c",
        "//sw/device/lib/dif/autogen:lc_ctrl_hdr",
        "//sw/device/lib/dif/autogen:lc_ctrl_src",
    ],
    hdrs = [
        "dif_lc_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_lc_ctrl",
        "//hw/top:lc_ctrl_c_regs",
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
        "dif_lc_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:lc_ctrl_unittest",
    ],
    deps = [
        ":lc_ctrl",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "mbx",
    srcs = [
        "dif_mbx.c",
        "//sw/device/lib/dif/autogen:mbx_hdr",
        "//sw/device/lib/dif/autogen:mbx_src",
    ],
    hdrs = [
        "dif_mbx.h",
    ],
    # TODO Update when we have a top with a keymgr_dpe.
    target_compatible_with = ["@platforms//:incompatible"],
    deps = [
        ":base",
        "//hw/top:dt_mbx",
        "//hw/top:mbx_c_regs",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "mbx_unittest",
    srcs = [
        "dif_mbx_unittest.cc",
        "//sw/device/lib/dif/autogen:mbx_unittest",
    ],
    deps = [
        ":mbx",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = [
        "dif_otbn.c",
        "//sw/device/lib/dif/autogen:otbn_hdr",
        "//sw/device/lib/dif/autogen:otbn_src",
    ],
    hdrs = [
        "dif_otbn.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_otbn",
        "//hw/top:otbn_c_regs",
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
        "dif_otbn_unittest.cc",
        "//sw/device/lib/dif/autogen:otbn_unittest",
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
        "dif_otp_ctrl.c",
        "//sw/device/lib/dif/autogen:otp_ctrl_hdr",
        "//sw/device/lib/dif/autogen:otp_ctrl_src",
    ],
    hdrs = [
        "dif_otp_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_otp_ctrl",
        "//hw/top:otp_ctrl_c_regs",
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
        "dif_otp_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:otp_ctrl_unittest",
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
        "dif_pattgen.c",
        "//sw/device/lib/dif/autogen:pattgen_hdr",
        "//sw/device/lib/dif/autogen:pattgen_src",
    ],
    hdrs = [
        "dif_pattgen.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_pattgen",
        "//hw/top:pattgen_c_regs",
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
        "dif_pattgen_unittest.cc",
        "//sw/device/lib/dif/autogen:pattgen_unittest",
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
        "dif_pinmux.c",
        "//sw/device/lib/dif/autogen:pinmux_hdr",
        "//sw/device/lib/dif/autogen:pinmux_src",
    ],
    hdrs = [
        "dif_pinmux.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_pinmux",
        "//hw/top:pinmux_c_regs",
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
        "dif_pinmux_unittest.cc",
        "//sw/device/lib/dif/autogen:pinmux_unittest",
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
        "dif_pwm.c",
        "//sw/device/lib/dif/autogen:pwm_hdr",
        "//sw/device/lib/dif/autogen:pwm_src",
    ],
    hdrs = [
        "dif_pwm.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_pwm",
        "//hw/top:pwm_c_regs",
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
        "//sw/device/lib/dif/autogen:pwm_unittest",
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
        "dif_pwrmgr.c",
        "//sw/device/lib/dif/autogen:pwrmgr_hdr",
        "//sw/device/lib/dif/autogen:pwrmgr_src",
    ],
    hdrs = [
        "dif_pwrmgr.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_pwrmgr",
        "//hw/top:pwrmgr_c_regs",
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
        "dif_pwrmgr_unittest.cc",
        "//sw/device/lib/dif/autogen:pwrmgr_unittest",
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
        "dif_rom_ctrl.c",
        "//sw/device/lib/dif/autogen:rom_ctrl_hdr",
        "//sw/device/lib/dif/autogen:rom_ctrl_src",
    ],
    hdrs = [
        "dif_rom_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_rom_ctrl",
        "//hw/top:rom_ctrl_c_regs",
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
        "//sw/device/lib/dif/autogen:rom_ctrl_unittest",
    ],
    deps = [
        ":rom_ctrl",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rstmgr_intf",
    srcs = ["//sw/device/lib/dif/autogen:rstmgr_hdr"],
    hdrs = ["dif_rstmgr.h"],
    deps = [":base"],
)

cc_library(
    name = "rstmgr",
    srcs = [
        "dif_rstmgr.c",
        "//sw/device/lib/dif/autogen:rstmgr_src",
    ],
    deps = [
        ":base",
        ":rstmgr_intf",
        "//hw/top:dt_rstmgr",
        "//hw/top:rstmgr_c_regs",
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
        "dif_rstmgr_unittest.cc",
        "//sw/device/lib/dif/autogen:rstmgr_unittest",
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
        "dif_rv_core_ibex.c",
        "//sw/device/lib/dif/autogen:rv_core_ibex_hdr",
        "//sw/device/lib/dif/autogen:rv_core_ibex_src",
    ],
    hdrs = [
        "dif_rv_core_ibex.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_rv_core_ibex",
        "//hw/top:rv_core_ibex_c_regs",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/runtime:hart",
    ],
)

cc_test(
    name = "rv_core_ibex_unittest",
    srcs = [
        "dif_rv_core_ibex_unittest.cc",
        "//sw/device/lib/dif/autogen:rv_core_ibex_unittest",
    ],
    deps = [
        ":rv_core_ibex",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_dm",
    srcs = [
        "dif_rv_dm.c",
        "//sw/device/lib/dif/autogen:rv_dm_hdr",
        "//sw/device/lib/dif/autogen:rv_dm_src",
    ],
    hdrs = [
        "dif_rv_dm.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_rv_dm",
        "//hw/top:rv_dm_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_test(
    name = "rv_dm_unittest",
    srcs = [
        "dif_rv_dm_unittest.cc",
        "//sw/device/lib/dif/autogen:rv_dm_unittest",
    ],
    deps = [
        ":rv_dm",
        ":test_base",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rv_plic",
    srcs = [
        "dif_rv_plic.c",
        "//sw/device/lib/dif/autogen:rv_plic_hdr",
        "//sw/device/lib/dif/autogen:rv_plic_src",
    ],
    hdrs = [
        "dif_rv_plic.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_rv_plic",
        "//hw/top:rv_plic_c_regs",
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
        "dif_rv_plic_unittest.cc",
        "//sw/device/lib/dif/autogen:rv_plic_unittest",
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
        "dif_rv_timer.c",
        "//sw/device/lib/dif/autogen:rv_timer_hdr",
        "//sw/device/lib/dif/autogen:rv_timer_src",
    ],
    hdrs = [
        "dif_rv_timer.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_rv_timer",
        "//hw/top:rv_timer_c_regs",
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
        "dif_rv_timer_unittest.cc",
        "//sw/device/lib/dif/autogen:rv_timer_unittest",
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
        "dif_spi_device.c",
        "//sw/device/lib/dif/autogen:spi_device_hdr",
        "//sw/device/lib/dif/autogen:spi_device_src",
    ],
    hdrs = [
        "dif_spi_device.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_spi_device",
        "//hw/top:spi_device_c_regs",
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
        "dif_spi_device_unittest.cc",
        "//sw/device/lib/dif/autogen:spi_device_unittest",
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
        "dif_spi_host.c",
        "//sw/device/lib/dif/autogen:spi_host_hdr",
        "//sw/device/lib/dif/autogen:spi_host_src",
    ],
    hdrs = [
        "dif_spi_host.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_spi_host",
        "//hw/top:spi_host_c_regs",
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
        "dif_spi_host_unittest.cc",
        "//sw/device/lib/dif/autogen:spi_host_unittest",
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
        "dif_sram_ctrl.c",
        "//sw/device/lib/dif/autogen:sram_ctrl_hdr",
        "//sw/device/lib/dif/autogen:sram_ctrl_src",
    ],
    hdrs = [
        "dif_sram_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_sram_ctrl",
        "//hw/top:sram_ctrl_c_regs",
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
        "dif_sram_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:sram_ctrl_unittest",
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
        "dif_sensor_ctrl.c",
        "//sw/device/lib/dif/autogen:sensor_ctrl_hdr",
        "//sw/device/lib/dif/autogen:sensor_ctrl_src",
    ],
    hdrs = [
        "dif_sensor_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_sensor_ctrl",
        "//hw/top:sensor_ctrl_c_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
    ],
)

cc_test(
    name = "sensor_ctrl_unittest",
    srcs = [
        "dif_sensor_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:sensor_ctrl_unittest",
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
        "dif_sysrst_ctrl.c",
        "//sw/device/lib/dif/autogen:sysrst_ctrl_hdr",
        "//sw/device/lib/dif/autogen:sysrst_ctrl_src",
    ],
    hdrs = [
        "dif_sysrst_ctrl.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_sysrst_ctrl",
        "//hw/top:sysrst_ctrl_c_regs",
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
        "dif_sysrst_ctrl_unittest.cc",
        "//sw/device/lib/dif/autogen:sysrst_ctrl_unittest",
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
        "dif_uart.c",
        "//sw/device/lib/dif/autogen:uart_hdr",
        "//sw/device/lib/dif/autogen:uart_src",
    ],
    hdrs = ["dif_uart.h"],
    deps = [
        ":base",
        "//hw/top:dt_uart",
        "//hw/top:uart_c_regs",
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
        "dif_uart_unittest.cc",
        "//sw/device/lib/dif/autogen:uart_unittest",
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
        "dif_usbdev.c",
        "//sw/device/lib/dif/autogen:usbdev_hdr",
        "//sw/device/lib/dif/autogen:usbdev_src",
    ],
    hdrs = [
        "dif_usbdev.h",
    ],
    deps = [
        ":base",
        "//hw/top:dt_usbdev",
        "//hw/top:usbdev_c_regs",
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
        "dif_usbdev_unittest.cc",
        "//sw/device/lib/dif/autogen:usbdev_unittest",
    ],
    deps = [
        ":test_base",
        ":usbdev",
        "@googletest//:gtest_main",
    ],
)
