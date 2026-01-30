# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_top")
load("@lowrisc_opentitan//hw/top_englishbreakfast/data/autogen:defs.bzl", "ENGLISHBREAKFAST_IPS")

ENGLISHBREAKFAST = opentitan_top(
    name = "englishbreakfast",
    hjson = "@lowrisc_opentitan//hw/top_englishbreakfast/data/autogen:top_englishbreakfast.gen.hjson",
    top_lib = "@lowrisc_opentitan//hw/top_englishbreakfast/sw/autogen:top_englishbreakfast",
    top_rtl = "@lowrisc_opentitan//hw/top_englishbreakfast:rtl_files",
    top_verilator_core = ["lowrisc:dv:top_englishbreakfast_chip_verilator_sim"],
    top_verilator_binary = {"binary": ["lowrisc_dv_top_englishbreakfast_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb"]},
    top_ld = "@lowrisc_opentitan//hw/top_englishbreakfast/sw/autogen:top_englishbreakfast_memory",
    ips = ENGLISHBREAKFAST_IPS,
    secret_cfgs = {
        "testing": "@lowrisc_opentitan//hw/top_englishbreakfast/data/autogen:top_englishbreakfast.secrets.testing.gen.hjson",
    },
)
