# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "opentitan_autogen_dif")
load("//hw/top:defs.bzl", "ALL_IP_NAMES")

package(default_visibility = ["//visibility:public"])

[
    opentitan_autogen_dif(
        name = ip,
        ip = ip,
        deps = [
            "//hw/top/dt:{}".format(ip),
            "//hw/top:{}_c_regs".format(ip),
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:base",
        ],
    )
    for ip in ALL_IP_NAMES
]
