# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

KEYMGR_DPE = opentitan_ip(
    name = "keymgr_dpe",
    hjson = "//hw/ip/keymgr_dpe/data:keymgr_dpe.hjson",
)
