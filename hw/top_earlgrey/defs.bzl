# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_earlgrey/data/autogen:defs.bzl", "EARLGREY_IPS")
load("//hw/top_earlgrey/data/otp:defs.bzl", "EARLGREY_STD_OTP_OVERLAYS")

EARLGREY = opentitan_top(
    name = "earlgrey",
    hjson = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    top_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    top_ld = "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    otp_map = "//hw/top_earlgrey/data/otp:otp_ctrl_mmap.hjson",
    std_otp_overlay = EARLGREY_STD_OTP_OVERLAYS,
    ips = EARLGREY_IPS,
)
