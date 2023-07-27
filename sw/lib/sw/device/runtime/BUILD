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
            "//sw/lib/sw/device/arch:device",
        ],
        shared = [
            "//sw/lib/sw/device/base:math",
            "//sw/lib/sw/device/base:stdasm",
            "//sw/lib/sw/device/base:macros",
        ],
    ),
)

cc_library(
    name = "ibex",
    srcs = ["ibex.c"],
    hdrs = ["ibex.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:stdasm",
    ],
)

cc_library(
    name = "irq",
    srcs = ["irq.c"],
    hdrs = ["irq.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:csr",
    ],
)

cc_library(
    name = "log",
    srcs = ["log.c"],
    hdrs = ["log.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:print",
    ],
)

cc_library(
    name = "pmp",
    srcs = ["pmp.c"],
    hdrs = ["pmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
    ],
)

cc_library(
    name = "print",
    hdrs = ["print.h"],
    deps = [
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:status",
    ],
)

filegroup(
    name = "print_c",
    srcs = ["print.c"],
)

filegroup(
    name = "print_unittest_cc",
    srcs = ["print_unittest.cc"],
)
