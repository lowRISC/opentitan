# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

LC_CTRL = opentitan_ip(
    name = "lc_ctrl",
    hjson = "@lowrisc_opentitan//hw/ip/lc_ctrl/data:lc_ctrl.hjson",
)
