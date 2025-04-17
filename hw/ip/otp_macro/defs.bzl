# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

OTP_MACRO = opentitan_ip(
    name = "otp_macro",
    hjson = "//hw/ip/otp_macro/data:otp_macro.hjson",
)
