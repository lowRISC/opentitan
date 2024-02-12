// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/second_rom_epmp.h"

#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/memory.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

// Symbols defined in linker script.
extern char _text_start[];             // Start of executable code.
extern char _text_end[];               // End of executable code.
extern char _rom_ext_virtual_start[];  // Start of ROM_EXT (VMA)
extern char _rom_ext_virtual_size[];   // Size of ROM_EXT (VMA)

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

void second_rom_epmp_state_init(lifecycle_state_t lc_state) {
  // Bring in-memory copy in line with the changes done in second_rom_start.S
  //
  // Note that the ePMP registers and their in-memory copy are carried over
  // from the Base ROM.
  const epmp_region_t second_rom_text = {.start = (uintptr_t)_text_start,
                                         .end = (uintptr_t)_text_end};
  epmp_state_unconfigure(0);
  epmp_state_unconfigure(1);
  epmp_state_unconfigure(2);
  epmp_state_configure_tor(5, second_rom_text, kEpmpPermLockedReadExecute);

  // Open Mailbox RAM and CTN and update Debug ROM access.
  const epmp_region_t ram_mbox = {.start = TOP_DARJEELING_RAM_MBOX_BASE_ADDR,
                                  .end = TOP_DARJEELING_RAM_MBOX_BASE_ADDR +
                                         TOP_DARJEELING_RAM_MBOX_SIZE_BYTES};
  const epmp_region_t ctn = {
      .start = TOP_DARJEELING_CTN_BASE_ADDR,
      .end = TOP_DARJEELING_CTN_BASE_ADDR + TOP_DARJEELING_CTN_SIZE_BYTES};
  const epmp_region_t debug_rom = {.start = TOP_DARJEELING_RV_DM_MEM_BASE_ADDR,
                                   .end = TOP_DARJEELING_RV_DM_MEM_BASE_ADDR +
                                          TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES};
  epmp_perm_t debug_rom_access = kEpmpPermLockedNoAccess;
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      debug_rom_access = kEpmpPermLockedReadWriteExecute;
      break;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      debug_rom_access = kEpmpPermLockedReadWriteExecute;
      break;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      debug_rom_access = kEpmpPermLockedNoAccess;
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      debug_rom_access = kEpmpPermLockedNoAccess;
      break;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      debug_rom_access = kEpmpPermLockedReadWriteExecute;
      break;
    default:
      HARDENED_TRAP();
  }
  // Update the hardware configuration (CSRs).
  //
  //            32           24             16             8             0
  //             +-------------+-------------+-------------+-------------+
  // `pmpcfg2` = | `pmp11cfg`  | `pmp10cfg`  | `pmp9cfg`   | `pmp8cfg`   |
  //             +-------------+-------------+-------------+-------------+
  // `pmpcfg3` = | `pmp15cfg`  | `pmp14cfg`  | `pmp13cfg`  | `pmp12cfg`  |
  //             +-------------+-------------+-------------+-------------+
  CSR_WRITE(CSR_REG_PMPADDR9,
            ram_mbox.start >> 2 | (ram_mbox.end - ram_mbox.start - 1) >> 3);
  CSR_WRITE(CSR_REG_PMPADDR10, ctn.start >> 2 | (ctn.end - ctn.start - 1) >> 3);
  CSR_WRITE(CSR_REG_PMPADDR13,
            debug_rom.start >> 2 | (debug_rom.end - debug_rom.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG2, 0xffff << 8);
  CSR_SET_BITS(CSR_REG_PMPCFG2,
               ((kEpmpModeNapot | kEpmpPermLockedReadWrite) << 8) |
                   ((kEpmpModeNapot | kEpmpPermLockedReadWrite) << 16));
  CSR_CLEAR_BITS(CSR_REG_PMPCFG3, 0xff << 8);
  CSR_SET_BITS(CSR_REG_PMPCFG3, (kEpmpModeNapot | debug_rom_access) << 8);
  // Update in-memory copy of ePMP register state
  epmp_state_configure_napot(9, ram_mbox, kEpmpPermLockedReadWrite);
  epmp_state_configure_napot(10, ctn, kEpmpPermLockedReadWrite);
  epmp_state_configure_napot(13, debug_rom, debug_rom_access);
}

void second_rom_epmp_unlock_rom_ext(epmp_region_t rom_ext_text,
                                    epmp_region_t rom_ext_lma) {
  const epmp_region_t rom_ext_vma = {.start = (uintptr_t)_rom_ext_virtual_start,
                                     .end = (uintptr_t)_rom_ext_virtual_start +
                                            (uintptr_t)_rom_ext_virtual_size};
  // Make sure rom_ext_text is a subset of rom_ext_vma
  HARDENED_CHECK_GE(rom_ext_text.start, rom_ext_vma.start);
  HARDENED_CHECK_LE(rom_ext_text.end, rom_ext_vma.end);
  // Update the hardware configuration (CSRs).
  //
  //            32          24          16           8           0
  //             +-----------+-----------+-----------+-----------+
  // `pmpcfg0` = | `pmp3cfg` | `pmp2cfg` | `pmp1cfg` | `pmp0cfg` |
  //             +-----------+-----------+-----------+-----------+
  CSR_WRITE(CSR_REG_PMPADDR0, rom_ext_text.start >> 2);
  CSR_WRITE(CSR_REG_PMPADDR1, rom_ext_text.end >> 2);
  CSR_WRITE(
      CSR_REG_PMPADDR2,
      rom_ext_vma.start >> 2 | (rom_ext_vma.end - rom_ext_vma.start - 1) >> 3);
  CSR_WRITE(
      CSR_REG_PMPADDR3,
      rom_ext_lma.start >> 2 | (rom_ext_lma.end - rom_ext_lma.start - 1) >> 3);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0xffffffff);
  CSR_SET_BITS(CSR_REG_PMPCFG0,
               ((kEpmpModeNapot | kEpmpPermLockedReadOnly) << 24) |
                   ((kEpmpModeNapot | kEpmpPermLockedReadOnly) << 16) |
                   ((kEpmpModeTor | kEpmpPermLockedReadExecute) << 8));
  // Update the in-memory copy of ePMP register state.
  epmp_state_configure_tor(1, rom_ext_text, kEpmpPermLockedReadExecute);
  epmp_state_configure_napot(2, rom_ext_vma, kEpmpPermLockedReadOnly);
  epmp_state_configure_napot(3, rom_ext_lma, kEpmpPermLockedReadOnly);
}
