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
IMM_ROM_EXT_SECTIONS = {
    "main": [
        "//sw/device/silicon_creator/imm_rom_ext:main_section_fpga_cw310",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_fpga_cw340",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_sim_dv_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_sim_verilator_base",
        "//sw/device/silicon_creator/imm_rom_ext:main_section_silicon_creator",
    ],
}
