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
        top = "//hw/top:top_desc",
    )
    for ip in ALL_IP_NAMES
]
