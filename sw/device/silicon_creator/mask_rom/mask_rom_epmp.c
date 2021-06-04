// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/mask_rom_epmp.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Symbols defined in linker script.
extern char _stack_start[];  // Lowest stack address.
extern char _text_start[];   // Start of executable code.
extern char _text_end[];     // End of executable code.

void mask_rom_epmp_state_init(epmp_state_t *state) {
  // Address space definitions.
  //
  // Note that the stack guard is placed at _stack_start because the stack
  // grows downward from _stack_end.
  const epmp_region_t rom_text = {.start = (uintptr_t)_text_start,
                                  .end = (uintptr_t)_text_end};
  const epmp_region_t rom = {.start = TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR,
                             .end = TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR +
                                    TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES};
  const epmp_region_t eflash = {
      .start = TOP_EARLGREY_EFLASH_BASE_ADDR,
      .end = TOP_EARLGREY_EFLASH_BASE_ADDR + TOP_EARLGREY_EFLASH_SIZE_BYTES};
  // TODO(#7117): generate MMIO addresses.
  const epmp_region_t mmio = {.start = 0x40000000, .end = 0x50000000};
  const epmp_region_t stack_guard = {.start = (uintptr_t)_stack_start,
                                     .end = (uintptr_t)_stack_start + 4};
  const epmp_region_t ram = {.start = TOP_EARLGREY_RAM_MAIN_BASE_ADDR,
                             .end = TOP_EARLGREY_RAM_MAIN_BASE_ADDR +
                                    TOP_EARLGREY_RAM_MAIN_SIZE_BYTES};

  // Initialize in-memory copy of ePMP register state.
  //
  // The actual hardware configuration is performed separately, either by reset
  // logic or in assembly. This code must be kept in sync with any changes
  // to the hardware configuration.
  *state = (epmp_state_t){0};
  epmp_state_configure_tor(state, 1, rom_text, kEpmpPermLockedReadExecute);
  epmp_state_configure_napot(state, 2, rom, kEpmpPermLockedReadOnly);
  epmp_state_configure_napot(state, 5, eflash, kEpmpPermLockedReadOnly);
  epmp_state_configure_tor(state, 11, mmio, kEpmpPermLockedReadWrite);
  epmp_state_configure_na4(state, 14, stack_guard, kEpmpPermLockedNoAccess);
  epmp_state_configure_napot(state, 15, ram, kEpmpPermLockedReadWrite);
  state->mseccfg = EPMP_MSECCFG_MMWP | EPMP_MSECCFG_RLB;
}

void mask_rom_epmp_unlock_rom_ext_rx(epmp_state_t *state, epmp_region_t image) {
  // Update the in-memory copy of ePMP register state.
  const int kEntry = 4;
  epmp_state_configure_tor(state, kEntry, image, kEpmpPermLockedReadExecute);

  // Update the hardware configuration (CSRs).
  //
  // Entry is hardcoded as 4. Make sure to modify hardcoded values if changing
  // kEntry.
  //
  // The `pmp4cfg` configuration is the first field in `pmpcfg1`.
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg1` = | `pmp7cfg` | `pmp6cfg` | `pmp5cfg` | `pmp4cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR3, image.start >> 2);
  CSR_WRITE(CSR_REG_PMPADDR4, image.end >> 2);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG1, 0xff);
  CSR_SET_BITS(CSR_REG_PMPCFG1, kEpmpModeTor | kEpmpPermLockedReadExecute);
}
