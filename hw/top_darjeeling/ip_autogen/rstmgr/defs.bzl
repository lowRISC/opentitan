# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

RSTMGR = opentitan_ip(
    name = "rstmgr",
    hjson = "@lowrisc_opentitan//hw/top_darjeeling/ip_autogen/rstmgr/data:rstmgr.hjson",
    ipconfig = "@lowrisc_opentitan//hw/top_darjeeling/ip_autogen/rstmgr/data:top_darjeeling_rstmgr.ipconfig.hjson",
    extension = "@lowrisc_opentitan//hw/top/dt:rstmgr_binding",
)
