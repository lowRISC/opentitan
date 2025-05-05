# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_englishbreakfast/data/autogen:defs.bzl", "ENGLISHBREAKFAST_IPS")

ENGLISHBREAKFAST = opentitan_top(
    name = "englishbreakfast",
    hjson = "//hw/top_englishbreakfast/data/autogen:top_englishbreakfast.gen.hjson",
    top_lib = "//hw/top_englishbreakfast/sw/autogen:top_englishbreakfast",
    top_ld = "//hw/top_englishbreakfast/sw/autogen:top_englishbreakfast_memory",
    ips = ENGLISHBREAKFAST_IPS,
)
