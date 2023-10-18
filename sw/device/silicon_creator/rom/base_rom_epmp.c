// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/base_rom_epmp.h"

#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/memory.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

// Symbols defined in linker script.
extern char _stack_start[];              // Lowest stack address.
extern char _text_start[];               // Start of executable code.
extern char _text_end[];                 // End of executable code.
extern char _second_rom_boot_address[];  // Start of Second ROM text.
extern char _epmp_reset_rx_size[];       // Size of ROM CRT text.

// Note: Hardcoding these values since the way we generate this range is not
// very robust at the moment. See #14345 and #14336.
static_assert(TOP_DARJEELING_MMIO_BASE_ADDR == 0x21100000,
              "MMIO region changed, update ePMP configuration if needed");
static_assert(TOP_DARJEELING_MMIO_SIZE_BYTES == 0xF501000,
              "MMIO region changed, update ePMP configuration if needed");

static_assert(TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR >=
                      TOP_DARJEELING_MMIO_BASE_ADDR &&
                  TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
                          TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES <=
                      TOP_DARJEELING_MMIO_BASE_ADDR +
                          TOP_DARJEELING_MMIO_SIZE_BYTES,
              "Retention SRAM must be in the MMIO address space.");

void base_rom_epmp_state_init(void) {
  // Address space definitions.
  //
  // Note that the stack guard is placed at _stack_start because the stack
  // grows downward from _stack_end.
  const epmp_region_t base_rom_text = {.start = (uintptr_t)_text_start,
                                       .end = (uintptr_t)_text_end};
  const epmp_region_t base_rom = {
      .start = TOP_DARJEELING_ROM0_BASE_ADDR,
      .end = TOP_DARJEELING_ROM0_BASE_ADDR + TOP_DARJEELING_ROM0_SIZE_BYTES};
  const epmp_region_t mmio = {
      .start = TOP_DARJEELING_MMIO_BASE_ADDR,
      .end = TOP_DARJEELING_MMIO_BASE_ADDR + TOP_DARJEELING_MMIO_SIZE_BYTES};
  const epmp_region_t debug_rom = {.start = TOP_DARJEELING_RV_DM_MEM_BASE_ADDR,
                                   .end = TOP_DARJEELING_RV_DM_MEM_BASE_ADDR +
                                          TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES};
  const epmp_region_t stack_guard = {.start = (uintptr_t)_stack_start,
                                     .end = (uintptr_t)_stack_start + 4};
  const epmp_region_t ram = {.start = TOP_DARJEELING_RAM_MAIN_BASE_ADDR,
                             .end = TOP_DARJEELING_RAM_MAIN_BASE_ADDR +
                                    TOP_DARJEELING_RAM_MAIN_SIZE_BYTES};

  // Initialize in-memory copy of ePMP register state.
  //
  // The actual hardware configuration is performed separately, either by reset
  // logic or in assembly. This code must be kept in sync with any changes
  // to the hardware configuration.
  memset(&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_tor(1, base_rom_text, kEpmpPermLockedReadExecute);
  epmp_state_configure_napot(2, base_rom, kEpmpPermLockedReadOnly);
  epmp_state_configure_tor(12, mmio, kEpmpPermLockedReadWrite);
  epmp_state_configure_napot(13, debug_rom, kEpmpPermLockedReadWriteExecute);
  epmp_state_configure_na4(14, stack_guard, kEpmpPermLockedNoAccess);
  epmp_state_configure_napot(15, ram, kEpmpPermLockedReadWrite);
  epmp_state.mseccfg = EPMP_MSECCFG_MMWP | EPMP_MSECCFG_RLB;
}

void base_rom_epmp_unlock_second_rom_rx(void) {
  const epmp_region_t second_rom_text = {
      .start = (uintptr_t)_second_rom_boot_address,
      .end =
          (uintptr_t)_second_rom_boot_address + (uintptr_t)_epmp_reset_rx_size};
  const epmp_region_t second_rom = {
      .start = TOP_DARJEELING_ROM1_BASE_ADDR,
      .end = TOP_DARJEELING_ROM1_BASE_ADDR + TOP_DARJEELING_ROM1_SIZE_BYTES};

  // Update the in-memory copy of ePMP register state.
  epmp_state_configure_tor(5, second_rom_text, kEpmpPermLockedReadExecute);
  epmp_state_configure_napot(6, second_rom, kEpmpPermLockedReadOnly);

  // Update the hardware configuration (CSRs).
  //
  //            32           24           16            8            0
  //             +------------+------------+------------+------------+
  // `pmpcfg1` = | `pmp7cfg`  | `pmp6cfg`  | `pmp5cfg`  | `pmp4cfg`  |
  //             +------------+------------+------------+------------+
  CSR_WRITE(CSR_REG_PMPADDR4, second_rom_text.start >> 2);
  CSR_WRITE(CSR_REG_PMPADDR5, second_rom_text.end >> 2);
  CSR_WRITE(CSR_REG_PMPADDR6, second_rom.start >> 2 |
                                  (second_rom.end - second_rom.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG1, 0xffff << 8);
  CSR_SET_BITS(CSR_REG_PMPCFG1,
               ((kEpmpModeTor | kEpmpPermLockedReadExecute) << 8) |
                   ((kEpmpModeNapot | kEpmpPermLockedReadOnly) << 16));
}

void base_rom_epmp_unlock_second_rom_patch_ram(epmp_region_t region) {
  // Update the in-memory copy of ePMP register state.
  epmp_state_configure_tor(8, region, kEpmpPermLockedReadExecute);

  // Update the hardware configuration (CSRs).
  //
  //            32           24           16            8            0
  //             +------------+------------+------------+------------+
  // `pmpcfg2` = | `pmp11cfg` | `pmp10cfg` | `pmp9cfg`  | `pmp8cfg`  |
  //             +------------+------------+------------+------------+
  CSR_WRITE(CSR_REG_PMPADDR7, region.start >> 2);
  CSR_WRITE(CSR_REG_PMPADDR8, region.end >> 2);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG2, 0xff);
  CSR_SET_BITS(CSR_REG_PMPCFG2, kEpmpModeTor | kEpmpPermLockedReadExecute);
}
