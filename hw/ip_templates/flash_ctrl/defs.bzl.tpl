# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

FLASH_CTRL = opentitan_ip(
    name = "flash_ctrl",
    hjson = "//hw/top_${topname}/ip_autogen/flash_ctrl:data/flash_ctrl.hjson",
)
