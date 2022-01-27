# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes_testutils",
    srcs = ["aes_testutils.c"],
    hdrs = ["aes_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
)

cc_library(
    name = "alert_handler_testutils",
    srcs = ["alert_handler_testutils.c"],
    hdrs = ["alert_handler_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/testing/test_framework",
    ],
)

cc_library(
    name = "aon_timer_testutils",
    srcs = ["aon_timer_testutils.c"],
    hdrs = ["aon_timer_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/testing/test_framework",
    ],
)

cc_library(
    name = "entropy_testutils",
    srcs = ["entropy_testutils.c"],
    hdrs = ["entropy_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/edn/data:edn_regs",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/testing/test_framework",
    ],
)

cc_library(
    name = "otp_ctrl_testutils",
    srcs = ["otp_ctrl_testutils.c"],
    hdrs = ["otp_ctrl_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework",
    ],
)

cc_library(
    name = "pwrmgr_testutils",
    srcs = ["pwrmgr_testutils.c"],
    hdrs = ["pwrmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/testing/test_framework",
    ],
)

cc_library(
    name = "rstmgr_testutils",
    srcs = ["rstmgr_testutils.c"],
    hdrs = ["rstmgr_testutils.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing/test_framework",
    ],
)

# TODO: Fix this.  This file isn't useful without test-status.h and should be
# considered part of the basic test_framework library.  As such, this file
# _should_ live along side those files.
filegroup(
    name = "check",
    srcs = ["check.h"],
)
