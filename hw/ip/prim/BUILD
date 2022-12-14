# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:verilog.bzl", "sv_library")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
    ],
)

sv_library(
    name = "prim_util_pkg",
    srcs = ["rtl/prim_util_pkg.sv"],
)

sv_library(
    name = "prim_assert",
    srcs = [
        "rtl/prim_assert_standard_macros.svh",
        "rtl/prim_assert.sv",
    ],
    deps = [":prim_util_pkg"],
)

sv_library(
    name = "prim_secded",
    srcs = glob(["rtl/prim_secded_*.sv"]),
    deps = [":prim_util_pkg"],
)

sv_library(
    name = "prim_mubi",
    srcs = glob(["rtl/prim_mubi*.sv"]),
)

sv_library(
    name = "prim_alert",
    srcs = [
        "rtl/prim_alert_pkg.sv",
        "rtl/prim_alert_receiver.sv",
        "rtl/prim_alert_sender.sv",
    ],
    deps = [
        ":prim_assert",
        ":prim_mubi",
    ],
)

sv_library(
    name = "prim",
    srcs = glob(["rtl/*.svh", "rtl/*.sv"]) + [],
)
