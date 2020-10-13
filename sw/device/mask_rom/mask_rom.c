// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/mask_rom/mask_rom.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/rom_exts/rom_ext_manifest_parser.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// This is the expected ROM_EXT Manifest Identifier
static const uint32_t kRomExtIdentifierExpected = 0x4552544F;

typedef void(boot_fn)(void);

void mask_rom_boot(void) {
  rom_ext_manifest_t rom_ext = rom_ext_get_parameters(kRomExtManifestSlotA);

  // Check we have a valid ROM_EXT
  if (rom_ext_get_identifier(rom_ext) == kRomExtIdentifierExpected) {
    // Set mtvec for ROM_EXT.
    uintptr_t interrupt_vector = rom_ext_get_interrupt_vector(rom_ext);
    asm volatile("csrw mtvec, %0" ::"r"(interrupt_vector));

    boot_fn *rom_ext_entry = (boot_fn *)rom_ext_get_entry(rom_ext);

    // Jump to ROM_EXT entry point.
    rom_ext_entry();
  } else {
    // Not yet implemented, intent is to throw simulation error.
    asm volatile("unimp");
  }
  while (true) {
    wait_for_interrupt();
  }
}

void mask_rom_exception_handler(void) { wait_for_interrupt(); }

void mask_rom_nmi_handler(void) { wait_for_interrupt(); }
