# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("//rules:linker.bzl", "ld_library")
load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

dual_cc_library(
    name = "top_earlgrey",
    srcs = [
        "top_earlgrey.c",
    ],
    hdrs = [
        "top_earlgrey.h",
        "top_earlgrey_memory.h",
    ],
    copts = dual_inputs(
        device = ["-flto=full"],
    ),
    target_compatible_with = dual_inputs(device = [OPENTITAN_CPU]),
    deps = ["//sw/device/lib/devicetables:dt_api"],
)

cc_library(
    name = "devicetables",
    srcs = ["devicetables.c"],
    copts = ["-flto=full"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":top_earlgrey",
        "//hw/top_earlgrey/sw/autogen/devicetables:dt_api_ipgen",
        "//sw/device/lib/devicetables",
        "//sw/device/lib/devicetables:dt_api",
    ],
)

ld_library(
    name = "top_earlgrey_memory",
    includes = ["top_earlgrey_memory.ld"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
