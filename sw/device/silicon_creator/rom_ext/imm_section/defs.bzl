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

IMM_SECTION_VARIATIONS = [
    "main",
]

# CAUTION: The message below should match the message defined in:
#   //sw/device/silicon_creator/rom_ext/imm_section/imm_section.c
IMMUTABLE_HASH_UNENFORCED_MSG = "hash unenforced"
