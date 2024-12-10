# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_earlgrey/data/autogen:defs.bzl", "EARLGREY")
load("//hw/top_darjeeling/data/autogen:defs.bzl", "DARJEELING")

ALL_TOPS = [
    EARLGREY,
    DARJEELING,
]

ALL_TOP_NAMES = [
    top.name
    for top in ALL_TOPS
]
