# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

RRAM_MACRO = opentitan_ip(
    name = "rram_macro",
    hjson = "//hw/ip/rram_macro/data:rram_macro.hjson",
)
