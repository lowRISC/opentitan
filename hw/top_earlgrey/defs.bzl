# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_earlgrey/data/autogen:defs.bzl", "EARLGREY_IPS")
load("//hw/top_earlgrey/data/otp:defs.bzl", "EARLGREY_OTP_SIGVERIFY_FAKE_KEYS", "EARLGREY_STD_OTP_OVERLAYS")

EARLGREY = opentitan_top(
    name = "earlgrey",
    hjson = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    top_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    top_rtl = "//hw/top_earlgrey:rtl_files",
    top_verilator_core = ["lowrisc:dv:top_earlgrey_chip_verilator_sim"],
    top_verilator_binary = {
        "binary": ["lowrisc_dv_top_earlgrey_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb"],
        "files_to_hash": ["lowrisc_dv_top_earlgrey_chip_verilator_sim_0.1/sim-verilator/src/"],
    },
    top_ld = "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    otp_map = "//hw/top_earlgrey/data/otp:otp_ctrl_mmap.hjson",
    std_otp_overlay = EARLGREY_STD_OTP_OVERLAYS,
    otp_sigverify_fake_keys = EARLGREY_OTP_SIGVERIFY_FAKE_KEYS,
    ips = EARLGREY_IPS,
    secret_cfgs = {
        "testing": "//hw/top_earlgrey/data/autogen:top_earlgrey.secrets.testing.gen.hjson",
    },
    silicon_creator_hooks = "//hw/top_earlgrey/sw/device/silicon_creator:hooks",
)

# These sizes should match the sizes in `hw/ip/rram_ctrl/rtl/rram_ctrl_pkg.sv`:
#   TotalBytes     = 2*1024*1024; // 2 MiB
#   TotalOtpBytes  = 2*1024 + 512 + 512; // (2.5 KiB data + 0.5 KiB integrity)
# _EARLGREY_NVM_SIZE = TotalBytes - TotalOtpBytes = 0x1FF400
# Info pages (real or emulated) are not OTP and are considered part of the NVM.
_EARLGREY_NVM_SIZE = "0x1FF400"

EARLGREY_SLOTS_NORMAL = {
    "nvm_size": _EARLGREY_NVM_SIZE,
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x100000",
    "owner_slot_a": "0x10000",
    "owner_slot_b": "0x110000",
    "rom_ext_size": "0x10000",
}

EARLGREY_SLOTS_COVERAGE = {
    "nvm_size": _EARLGREY_NVM_SIZE,
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x100000",
    "owner_slot_a": "0x20000",
    "owner_slot_b": "0x120000",
    "rom_ext_size": "0x20000",
}

EARLGREY_SLOTS = select({
    "@lowrisc_opentitan//rules/coverage:enabled": EARLGREY_SLOTS_COVERAGE,
    "//conditions:default": EARLGREY_SLOTS_NORMAL,
})
