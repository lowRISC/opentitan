# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_rust_header",
)

package(default_visibility = ["//visibility:public"])

alias(
    name = "top",
    actual = "//hw/top_earlgrey",
)

# List of IPs for which to generate headers.
IPS = [
    "flash_ctrl",
    "clkmgr",
    "rstmgr",
    "rv_plic",
    "pwrmgr",
]

[
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
        top = ":top",
    )
    for ip in IPS
]

[
    opentitan_ip_rust_header(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        top = ":top",
    )
    for ip in IPS
]
