# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

PATTGEN = opentitan_ip(
    name = "pattgen",
    hjson = "//hw/ip/pattgen/data:pattgen.hjson",
)
