# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

I3C = opentitan_ip(
    name = "i3c",
    hjson = "//hw/ip/i3c/data:i3c.hjson",
)
