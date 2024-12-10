# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

SRAM_CTRL = opentitan_ip(
    name = "sram_ctrl",
    hjson = "//hw/ip/sram_ctrl/data:sram_ctrl.hjson",
)
