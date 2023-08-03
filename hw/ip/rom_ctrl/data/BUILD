# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_hjson_header")

autogen_hjson_header(
    name = "rom_ctrl_regs",
    srcs = [
        "rom_ctrl.hjson",
    ],
    node = "regs",
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
