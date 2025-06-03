# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_earlgrey/data/autogen:defs.bzl", "EARLGREY_IPS")

EARLGREY = opentitan_top(
    name = "earlgrey",
    hjson = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    top_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    top_ld = "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    otp_ctrl_mmap = "//hw/top_earlgrey/data/otp:otp_ctrl_mmap.hjson",
    std_otp_overlay = "//hw/top_earlgrey/data/otp:std_otp_overlay",
    ips = EARLGREY_IPS,
)
