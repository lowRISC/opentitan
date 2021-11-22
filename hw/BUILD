# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:fusesoc.bzl", "fusesoc_build")

package(default_visibility = ["//visibility:public"])

fusesoc_build(
    name = "verilator",
    srcs = [
        ":all_files",
    ],
    cores = [
        "//:cores",
    ],
    systems = ["lowrisc:dv:chip_verilator_sim"],
    target = "sim",
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/ip:all_files",
        "//hw/top_earlgrey:all_files",
    ],
)
