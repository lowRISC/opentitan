# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:cc.bzl", "exec_env_filegroup")

package(default_visibility = ["//visibility:public"])

exec_env_filegroup(
    name = "mask_rom",
    testonly = True,
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310": "cw310",
        "//hw/top_earlgrey:fpga_cw340": "cw340",
        "//hw/top_earlgrey:sim_dv_base": "dv",
        "//hw/top_earlgrey:sim_verilator_base": "verilator",
        "//hw/top_earlgrey:sim_qemu_base": "qemu",
        "//hw/top_earlgrey:silicon_creator": "silicon",
    },
    files = {
        "files/mask_rom_fpga_cw310.39.scr.vmem": "cw310",
        "files/mask_rom_fpga_cw340.39.scr.vmem": "cw340",
        "files/mask_rom_sim_dv.39.scr.vmem": "dv",
        "files/mask_rom_sim_verilator.39.scr.vmem": "verilator",
        "files/mask_rom_sim_qemu_base.elf": "qemu",
        "files/mask_rom_silicon_creator.39.scr.vmem": "silicon",
    },
    kind = "rom",
    rom = {
        "files/mask_rom_fpga_cw310.39.scr.vmem": "cw310",
        "files/mask_rom_fpga_cw340.39.scr.vmem": "cw340",
        "files/mask_rom_sim_dv.39.scr.vmem": "dv",
        "files/mask_rom_sim_verilator.39.scr.vmem": "verilator",
        "files/mask_rom_sim_qemu_base.elf": "qemu",
        "files/mask_rom_silicon_creator.39.scr.vmem": "silicon",
    },
)
