# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

OTP_CTRL = opentitan_ip(
    name = "otp_ctrl",
    hjson = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/otp_ctrl/data:otp_ctrl.hjson",
    ipconfig = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/otp_ctrl/data:top_earlgrey_otp_ctrl.ipconfig.hjson",
    extension = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/otp_ctrl/util:dt",
    dt_src_deps = ["@lowrisc_opentitan//hw/top:otp_ctrl_c_regs"],
)
