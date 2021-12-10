# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

# TODO use more specific targets to avoid unnecesary dependencies
# https://github.com/lowRISC/opentitan/issues/9098
cc_library(
    name = "test_framework",
    srcs = [
        "test_coverage_none.c",
        "test_status.c",
    ],
    hdrs = [
        "test_coverage.h",
        "test_status.h",
        "//sw/device/lib/testing:check",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
    ],
)

cc_library(
    name = "ottf_isrs",
    srcs = [
        "ottf_isrs.S",
        "ottf_isrs.c",
    ],
    hdrs = [
        "ottf_isrs.h",
        "ottf_macros.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
    ],
)
