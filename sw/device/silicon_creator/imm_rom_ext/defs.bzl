# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The target list should contian prebuilt artifacts and run-time build targets.
IMM_ROM_EXT_TARGETS = {
    "nop": "//sw/device/silicon_creator/imm_rom_ext/prebuilts:nop_imm_rom_ext",
    "hello_world": "//sw/device/silicon_creator/imm_rom_ext:hello_world_section",
}
