# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_list_flag")
load("//rules:fusesoc.bzl", "fusesoc_build")
load("//hw/top:defs.bzl", "opentitan_select_top_attr")

filegroup(
    name = "rtl_files",
    srcs = glob(
        ["**"],
    ) + [
        "//hw/top_earlgrey:rtl_files",  # Add Earlgrey RTL files for alert_handler_pkg and top_pkg
        "//hw/top_englishbreakfast/dv/verilator:all_files",
        "//hw/top_englishbreakfast/ip:rtl_files",
    ],
    visibility = ["//visibility:public"],
)
