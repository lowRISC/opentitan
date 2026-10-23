# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "OPENTITAN_BASE_PLATFORM",
)

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

platform(
    name = "platform",
    flags = [
        "--features=-rv32_bitmanip",
    ],
    parents = [OPENTITAN_BASE_PLATFORM],
)
