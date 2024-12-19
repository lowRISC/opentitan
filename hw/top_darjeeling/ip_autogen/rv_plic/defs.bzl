# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RV_PLIC = opentitan_ip(
    name = "rv_plic",
    hjson = "//hw/top_darjeeling/ip_autogen/rv_plic:data/rv_plic.hjson",
)
