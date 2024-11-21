// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"

#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

enum {
  kFlashHalf = TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2,
};

const manifest_t *rom_ext_manifest(void) {
  uintptr_t pc = 0;
  asm("auipc %[pc], 0;" : [pc] "=r"(pc));

  // Align the PC to the current flash side.  The ROM_EXT must be the first
  // entity in each flash side, so this alignment is the manifest address.
  pc &= ~((uintptr_t)kFlashHalf - 1);
  return (const manifest_t *)pc;
}
