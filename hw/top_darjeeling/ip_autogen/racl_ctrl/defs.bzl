# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

RACL_CTRL = opentitan_ip(
    name = "racl_ctrl",
    hjson = "@lowrisc_opentitan//hw/top_darjeeling/ip_autogen/racl_ctrl/data:racl_ctrl.hjson",
)
