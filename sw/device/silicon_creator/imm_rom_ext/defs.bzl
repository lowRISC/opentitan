# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The target list should contian prebuilt artifacts and run-time build targets.
IMM_ROM_EXT_TARGETS = {
    "main": "//sw/device/silicon_creator/imm_rom_ext:main_section",
}

# CAUTION: The message below should match the message defined in:
#   //sw/device/silicon_creator/imm_rom_ext/imm_rom_ext.c
IMMUTABLE_HASH_UNENFORCED_MSG = "hash unenforced"
