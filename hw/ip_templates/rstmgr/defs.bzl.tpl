# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RSTMGR = opentitan_ip(
    name = "rstmgr",
    hjson = "//hw/top_${topname}/ip_autogen/rstmgr:data/rstmgr.hjson",
    ipconfig = "//hw/top_${topname}/ip_autogen/rstmgr:data/top_${topname}_rstmgr.ipconfig.hjson",
    extension = "//hw/top_${topname}/ip_autogen/rstmgr/util:dt",
)
