# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

CHERIOT = opentitan_ip(
    name = "cheriot",
    hjson = "//hw/ip/cheriot/data:cheriot.hjson",
)
