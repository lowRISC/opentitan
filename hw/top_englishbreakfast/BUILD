# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")
load("//rules:fusesoc.bzl", "fusesoc_build")

filegroup(
    name = "rtl_files",
    srcs = glob(
        ["**"],
    ) + [
        "//hw/top_englishbreakfast/ip:rtl_files",
    ],
    visibility = ["//visibility:public"],
)

fusesoc_build(
    name = "verilator_sim",
    srcs = [
        ":rtl_files",
        "//hw:dpi_files",
        "//hw:dv_common_files",
        "//hw:rtl_files",
        "//hw:verilator_files",
        "//hw/ip:verilator_files",
    ],
    cores = [
        "//hw:cores",
    ],
    data = ["//hw/ip/otbn:rtl_files"],
    make_options = ":make_options",
    output_groups = {
        "binary": ["sim-verilator/Vchip_englishbreakfast_verilator"],
    },
    systems = ["lowrisc:systems:chip_englishbreakfast_verilator"],
    tags = [
        "manual",
        "verilator",
    ],
    target = "sim",
    verilator_options = ":verilator_options",
)

string_list_flag(
    name = "verilator_options",
    build_setting_default = [
        "--threads",
        "2",
    ],
)

string_list_flag(
    name = "make_options",
    build_setting_default = [
        "-j",
        "2",
    ],
)
