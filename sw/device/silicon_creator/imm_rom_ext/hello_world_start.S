// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO(#24368): Adapt the startup assembly for real IMM_ROM_EXT. This startup
// assembly only works for hello-world IMM_ROM_EXT.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

  .balign 4
  .global _imm_rom_ext_start_boot
  .type _imm_rom_ext_start_boot, @function
_imm_rom_ext_start_boot:
  tail imm_rom_ext_main
  .size _imm_rom_ext_start_boot, .-_imm_rom_ext_start_boot
