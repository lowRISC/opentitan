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
    name = "and2",
    srcs = ["rtl/prim_generic_and2.sv"],
)
