# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RV_DM = opentitan_ip(
    name = "rv_dm",
    hjson = "//hw/ip/rv_dm/data:rv_dm.hjson",
)
