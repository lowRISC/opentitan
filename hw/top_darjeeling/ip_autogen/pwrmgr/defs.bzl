# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

PWRMGR = opentitan_ip(
    name = "pwrmgr",
    hjson = "//hw/top_darjeeling/ip_autogen/pwrmgr:data/pwrmgr.hjson",
    ipconfig = "//hw/top_darjeeling/ip_autogen/pwrmgr:data/top_darjeeling_pwrmgr.ipconfig.hjson",
    extension = "//hw/top_darjeeling/ip_autogen/pwrmgr/util:dt",
)
