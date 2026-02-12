# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

OTP_CTRL = opentitan_ip(
    name = "otp_ctrl",
    hjson = "//hw/top_${topname}/ip_autogen/otp_ctrl/data:otp_ctrl.hjson",
    ipconfig = "//hw/top_${topname}/ip_autogen/otp_ctrl/data:top_${topname}_otp_ctrl.ipconfig.hjson",
    extension = "//hw/top_${topname}/ip_autogen/otp_ctrl/util:dt",
    dt_src_deps = ["//hw/top:otp_ctrl_c_regs"],
)
