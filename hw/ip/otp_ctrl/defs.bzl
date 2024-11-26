# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

OTP_CTRL = opentitan_ip(
    name = "otp_ctrl",
    hjson = "//hw/ip/otp_ctrl/data:otp_ctrl.hjson",
)
