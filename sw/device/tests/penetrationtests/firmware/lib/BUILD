# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "extclk_sca_fi",
    srcs = ["extclk_sca_fi.c"],
    hdrs = ["extclk_sca_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/penetrationtests/json:extclk_sca_fi_commands",
    ],
)

cc_library(
    name = "pentest_lib",
    srcs = ["pentest_lib.c"],
    hdrs = ["pentest_lib.h"],
    deps = [
        "//hw/ip/aes:model",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:csrng_shared",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/penetrationtests/json:pentest_lib_commands",
    ] + select({
        "//sw/device:is_english_breakfast": [],
        "//conditions:default": [
            "//sw/device/lib/crypto/drivers:otbn",
            "//sw/device/lib/testing:entropy_testutils",
        ],
    }),
)
