# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

RV_PLIC = opentitan_ip(
    name = "rv_plic",
    hjson = "@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/rv_plic/data:rv_plic.hjson",
)
