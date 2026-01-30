# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_top")
load("@lowrisc_opentitan//hw/top_darjeeling/data/autogen:defs.bzl", "DARJEELING_IPS")
load("@lowrisc_opentitan//hw/top_darjeeling/data/otp:defs.bzl", "DARJEELING_OTP_SIGVERIFY_FAKE_KEYS", "DARJEELING_STD_OTP_OVERLAYS")

DARJEELING = opentitan_top(
    name = "darjeeling",
    hjson = "@lowrisc_opentitan//hw/top_darjeeling/data/autogen:top_darjeeling.gen.hjson",
    top_lib = "@lowrisc_opentitan//hw/top_darjeeling/sw/autogen:top_darjeeling",
    top_rtl = "@lowrisc_opentitan//hw/top_darjeeling:rtl_files",
    top_verilator_core = ["lowrisc:dv:top_darjeeling_chip_verilator_sim"],
    top_verilator_binary = {"binary": ["lowrisc_dv_top_darjeeling_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb"]},
    top_ld = "@lowrisc_opentitan//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
    otp_map = "@lowrisc_opentitan//hw/top_darjeeling/data/otp:otp_ctrl_mmap.hjson",
    std_otp_overlay = DARJEELING_STD_OTP_OVERLAYS,
    otp_sigverify_fake_keys = DARJEELING_OTP_SIGVERIFY_FAKE_KEYS,
    ips = DARJEELING_IPS,
    secret_cfgs = {
        "testing": "@lowrisc_opentitan//hw/top_darjeeling/data/autogen:top_darjeeling.secrets.testing.gen.hjson",
    },
)
