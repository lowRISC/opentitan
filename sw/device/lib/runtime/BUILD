# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "epmp",
    srcs = ["epmp.c"],
    hdrs = ["epmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
)

dual_cc_library(
    name = "hart",
    srcs = dual_inputs(
        device = ["hart.c"],
        host = ["hart_polyfills.c"],
    ),
    hdrs = ["hart.h"],
    deps = dual_inputs(
        device = [
            ":ibex",
            "//sw/device/lib/arch:device",
        ],
        shared = [
            "//sw/device/lib/base:math",
            "//sw/device/lib/base:stdasm",
            "//sw/device/lib/base:macros",
        ],
    ),
)

cc_library(
    name = "ibex",
    srcs = ["ibex.c"],
    hdrs = ["ibex.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:stdasm",
    ],
)

cc_library(
    name = "irq",
    srcs = ["irq.c"],
    hdrs = ["irq.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:csr",
    ],
)

cc_library(
    name = "log",
    srcs = ["log.c"],
    hdrs = ["log.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/runtime:print",
    ],
)

cc_library(
    name = "pmp",
    srcs = ["pmp.c"],
    hdrs = ["pmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "print",
    srcs = ["print.c"],
    hdrs = ["print.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
    ],
)

cc_test(
    name = "print_unittest",
    srcs = ["print_unittest.cc"],
    deps = [
        ":print",
        "@com_google_absl//absl/strings:str_format",
        "@googletest//:gtest_main",
    ],
)
