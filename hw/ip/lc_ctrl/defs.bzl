# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

LC_CTRL = opentitan_ip(
    name = "lc_ctrl",
    hjson = "//hw/ip/lc_ctrl/data:lc_ctrl.hjson",
)
