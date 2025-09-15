# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

CLKMGR = opentitan_ip(
    name = "clkmgr",
    hjson = "//hw/top_verbano/ip_autogen/clkmgr/data:clkmgr.hjson",
    ipconfig = "//hw/top_verbano/ip_autogen/clkmgr/data:top_verbano_clkmgr.ipconfig.hjson",
    extension = "//hw/top_verbano/ip_autogen/clkmgr/util:dt",
    dt_hdr_deps = ["//sw/device/lib/base:bitfield"],
    dt_src_deps = ["//hw/top:clkmgr_c_regs"],
)
