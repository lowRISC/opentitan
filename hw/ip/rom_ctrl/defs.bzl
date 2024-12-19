# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

ROM_CTRL = opentitan_ip(
    name = "rom_ctrl",
    hjson = "//hw/ip/rom_ctrl/data:rom_ctrl.hjson",
)
