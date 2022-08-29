// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Note: Since this test program is written to verify the behavior of the ROM C
// exception handlers,
// - it does not have a `.crt` section,
// - its entrypoint `_rom_ext_start_boot()` is defined here and it doesn't have
// a `rom_ext_main()` function, and
// - it has has only the following sections:
//   - `.manifest`, to be able to boot this program from ROM,
//   - `.text`, only 2 instructions to trigger an instruction access fault, and
//   - `.static_critical`, required by the linker script.

void _rom_ext_start_boot(void) {
  ((void (*)(void))TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR)();
}
