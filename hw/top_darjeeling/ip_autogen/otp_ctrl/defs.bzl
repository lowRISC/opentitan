# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

OTP_CTRL = opentitan_ip(
    name = "otp_ctrl",
    hjson = "//hw/top_darjeeling/ip_autogen/otp_ctrl/data:otp_ctrl.hjson",
    ipconfig = "//hw/top_darjeeling/ip_autogen/otp_ctrl/data:top_darjeeling_otp_ctrl.ipconfig.hjson",
    extension = "//hw/top_darjeeling/ip_autogen/otp_ctrl/util:dt",
    dt_src_deps = ["//hw/top:otp_ctrl_c_regs"],
)
