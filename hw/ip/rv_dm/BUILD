# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

opentitan_ip(
    name = "rv_dm",
    doc = glob(["doc/**"]),
    hjson = "//hw/ip/rv_dm/data:hjson",
    rtl = glob([
        "dv/**",
        "rtl/**",
        "lint/**",
        "*.core",
    ]),
)
