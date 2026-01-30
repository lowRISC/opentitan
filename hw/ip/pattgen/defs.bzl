# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

PATTGEN = opentitan_ip(
    name = "pattgen",
    hjson = "@lowrisc_opentitan//hw/ip/pattgen/data:pattgen.hjson",
)
