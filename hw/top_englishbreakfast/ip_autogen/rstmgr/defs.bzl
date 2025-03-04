# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RSTMGR = opentitan_ip(
    name = "rstmgr",
    hjson = "//hw/top_englishbreakfast/ip_autogen/rstmgr:data/rstmgr.hjson",
    ipconfig = "//hw/top_englishbreakfast/ip_autogen/rstmgr:data/top_englishbreakfast_rstmgr.ipconfig.hjson",
    extension = "//hw/top_englishbreakfast/ip_autogen/rstmgr/util:dt",
)
