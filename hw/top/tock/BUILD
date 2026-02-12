# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "opentitan_ip_rust_module")
load("//hw/top:defs.bzl", "ALL_IP_NAMES")

package(default_visibility = ["//visibility:public"])

# Rust Tock register modules for all IPs.
[
    opentitan_ip_rust_module(
        name = "{}_regs".format(ip),
        ip = ip,
        kind = "tock",
    )
    for ip in ALL_IP_NAMES
]
