# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_top")
load("@lowrisc_opentitan//hw/top_earlgrey/data/autogen:defs.bzl", "EARLGREY_IPS")
load("@lowrisc_opentitan//hw/top_earlgrey/data/otp:defs.bzl", "EARLGREY_OTP_SIGVERIFY_FAKE_KEYS", "EARLGREY_STD_OTP_OVERLAYS")

EARLGREY = opentitan_top(
    name = "earlgrey",
    hjson = "@lowrisc_opentitan//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    top_lib = "@lowrisc_opentitan//hw/top_earlgrey/sw/autogen:top_earlgrey",
    top_rtl = "@lowrisc_opentitan//hw/top_earlgrey:rtl_files",
    top_verilator_core = ["lowrisc:dv:top_earlgrey_chip_verilator_sim"],
    top_verilator_binary = {"binary": ["lowrisc_dv_top_earlgrey_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb"]},
    top_ld = "@lowrisc_opentitan//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    otp_map = "@lowrisc_opentitan//hw/top_earlgrey/data/otp:otp_ctrl_mmap.hjson",
    std_otp_overlay = EARLGREY_STD_OTP_OVERLAYS,
    otp_sigverify_fake_keys = EARLGREY_OTP_SIGVERIFY_FAKE_KEYS,
    ips = EARLGREY_IPS,
    secret_cfgs = {
        "testing": "@lowrisc_opentitan//hw/top_earlgrey/data/autogen:top_earlgrey.secrets.testing.gen.hjson",
    },
    silicon_creator_hooks = "@lowrisc_opentitan//hw/top_earlgrey/sw/device/silicon_creator:hooks",
)

EARLGREY_SLOTS = {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x10000",
    "owner_slot_b": "0x90000",
    "rom_ext_size": "0x10000",
}
