# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:verilog.bzl", "sv_library", "sv_list")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/ip/uart/data:all_files",
    ],
)

sv_library(
    name = "uart",
    srcs = [
        "rtl/uart_rx.sv",
        "rtl/uart_tx.sv",
        "rtl/uart_core.sv",
        "rtl/uart_reg_pkg.sv",
        "rtl/uart_reg_top.sv",
        "rtl/uart.sv",
    ],
    deps = [
        "//hw/ip/prim:prim_alert",
        "//hw:and2",
    ],
)

sv_list(
    name = "uart_list",
    deps = [
        ":uart",
    ],
)
