# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

opentitan_ip(
    name = "keymgr_dpe",
    doc = glob(["doc/**"]),
    hjson = "//hw/ip/keymgr_dpe/data:hjson",
    rtl = glob([
        "dv/**",
        "rtl/**",
        "lint/**",
        "*.core",
    ]),
)

filegroup(
    name = "cores",
    srcs = glob(["**/*.core"]),
)
