# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "isr_testutils",
    srcs = ["isr_testutils.c"],
    hdrs = ["isr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:adc_ctrl",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pattgen",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

cc_library(
    name = "pinmux",
    srcs = ["pinmux.c"],
    hdrs = ["pinmux.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/ujson",
    ],
)
