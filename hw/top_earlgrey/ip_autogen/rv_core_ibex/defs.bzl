# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RV_CORE_IBEX = opentitan_ip(
    name = "rv_core_ibex",
    hjson = "//hw/top_earlgrey/ip_autogen/rv_core_ibex:data/rv_core_ibex.hjson",
)
