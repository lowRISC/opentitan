# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

CLKMGR = opentitan_ip(
    name = "clkmgr",
    hjson = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/clkmgr/data:clkmgr.hjson",
    ipconfig = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/clkmgr/data:top_earlgrey_clkmgr.ipconfig.hjson",
    extension = "@lowrisc_opentitan//hw/top/dt:clkmgr_binding",
    dt_hdr_deps = ["@lowrisc_opentitan//sw/device/lib/base:bitfield"],
    dt_src_deps = ["@lowrisc_opentitan//hw/top:clkmgr_c_regs"],
)
