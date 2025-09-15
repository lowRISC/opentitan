# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

BKDR_LOADER = opentitan_ip(
    name = "bkdr_loader",
    hjson = "//hw/ip/bkdr_loader/data:bkdr_loader.hjson",
)
