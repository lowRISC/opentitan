# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

CLKMGR = opentitan_ip(
    name = "clkmgr",
    hjson = "//hw/top_${topname}/ip_autogen/clkmgr:data/clkmgr.hjson",
)
