# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

OTBN = opentitan_ip(
    name = "otbn",
    hjson = "//hw/ip/otbn/data:otbn.hjson",
)
