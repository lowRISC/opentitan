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
    name = "sca_lib",
    srcs = ["sca_lib.c"],
    hdrs = ["sca_lib.h"],
    deps = [
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:csrng_shared",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
    ],
)
