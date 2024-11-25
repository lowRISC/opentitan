# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/ip/keymgr/data:all_files",
    ],
)

opentitan_ip(
    name = "keymgr",
    hjson = "//hw/ip/keymgr/data:hjson",
)
