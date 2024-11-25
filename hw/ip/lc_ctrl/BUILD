# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/ip/lc_ctrl/data:all_files",
    ],
)

opentitan_ip(
    name = "lc_ctrl",
    hjson = "//hw/ip/lc_ctrl/data:hjson",
)
