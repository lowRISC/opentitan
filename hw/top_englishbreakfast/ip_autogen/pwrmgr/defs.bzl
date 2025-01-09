# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

PWRMGR = opentitan_ip(
    name = "pwrmgr",
    hjson = "//hw/top_englishbreakfast/ip_autogen/pwrmgr:data/pwrmgr.hjson",
)
