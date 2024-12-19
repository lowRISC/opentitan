# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

AON_TIMER = opentitan_ip(
    name = "aon_timer",
    hjson = "//hw/ip/aon_timer/data:aon_timer.hjson",
)
