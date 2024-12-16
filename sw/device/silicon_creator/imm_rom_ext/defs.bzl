# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

DEFAULT_EXEC_ENV = [
    "//hw/top_earlgrey:fpga_cw310",
    "//hw/top_earlgrey:fpga_cw340",
    "//hw/top_earlgrey:sim_dv_base",
    "//hw/top_earlgrey:sim_verilator_base",
    "//hw/top_earlgrey:silicon_creator",
]

# The target list should contian prebuilt artifacts and run-time build targets.
SLOT_A_IMM_ROM_EXT_SECTIONS = {
    "main": [
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_a_fpga_cw310",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_a_fpga_cw340",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_a_sim_dv_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_a_sim_verilator_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_a_silicon_creator",
    ],
}

SLOT_B_IMM_ROM_EXT_SECTIONS = {
    "main": [
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_b_fpga_cw310",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_b_fpga_cw340",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_b_sim_dv_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_b_sim_verilator_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_b_silicon_creator",
    ],
}

SLOT_VIRTUAL_IMM_ROM_EXT_SECTIONS = {
    "main": [
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_virtual_fpga_cw310",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_virtual_fpga_cw340",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_virtual_sim_dv_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_virtual_sim_verilator_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_slot_virtual_silicon_creator",
    ],
}
