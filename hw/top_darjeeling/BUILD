# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_hjson_header")

autogen_hjson_header(
    name = "rv_plic_regs",
    srcs = [
        "ip_autogen/rv_plic/data/rv_plic.hjson",
    ],
)

autogen_hjson_header(
    name = "alert_handler_regs",
    srcs = [
        "ip_autogen/alert_handler/data/alert_handler.hjson",
    ],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/top_earlgrey/data:all_files",
        "//hw/top_earlgrey/dv/verilator:all_files",
        "//hw/top_earlgrey/ip:all_files",
        "//hw/top_earlgrey/sw:all_files",
    ],
)
