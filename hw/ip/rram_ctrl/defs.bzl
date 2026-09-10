# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RRAM_CTRL = opentitan_ip(
    name = "rram_ctrl",
    hjson = "//hw/ip/rram_ctrl/data:rram_ctrl.hjson",
)
