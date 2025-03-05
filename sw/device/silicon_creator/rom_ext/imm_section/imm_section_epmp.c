// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/imm_section/imm_section_epmp.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/epmp.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// Address populated by the linker.
extern char _rom_ext_immutable_start[];
extern char _rom_ext_immutable_end[];
extern char _text_end[];
extern char _stack_start[];  // Lowest stack address.

static const epmp_region_t kMmioRegion = {
    .start = TOP_EARLGREY_MMIO_BASE_ADDR,
    .end = TOP_EARLGREY_MMIO_BASE_ADDR + TOP_EARLGREY_MMIO_SIZE_BYTES,
};

static const epmp_region_t kFlashRegion = {
    .start = TOP_EARLGREY_EFLASH_BASE_ADDR,
    .end = TOP_EARLGREY_EFLASH_BASE_ADDR + TOP_EARLGREY_EFLASH_SIZE_BYTES,
};

static const epmp_region_t kRvDmRegion = {
    .start = TOP_EARLGREY_RV_DM_MEM_BASE_ADDR,
    .end = TOP_EARLGREY_RV_DM_MEM_BASE_ADDR + TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES,
};

static const epmp_region_t kStackGuard = {.start = (uintptr_t)_stack_start,
                                          .end = (uintptr_t)_stack_start + 4};

static const epmp_region_t kImmTextRegion = {
    .start = (uintptr_t)_rom_ext_immutable_start,
    .end = (uintptr_t)_text_end,
};

rom_error_t imm_section_epmp_reconfigure(void) {
  // ePMP region 15 gives read/write access to RAM.
  // Leave it unchanged.

  // Reconfigure the ePMP MMIO region to be NAPOT region 14, thus freeing
  // up an ePMP entry for use elsewhere.
  epmp_set_napot(14, kMmioRegion, kEpmpPermLockedReadWrite);

  // ePMP region 11 protects the stack from overflow.
  // This stack guard was in ePMP region 14.
  epmp_set_napot(11, kStackGuard, kEpmpPermLockedNoAccess);

  // ePMP region 12 allows RvDM access.
  // This RvDM region was in ePMP region 13.
  if (lifecycle_is_prod() == kHardenedBoolTrue) {
    // No RvDM access in Prod states, so we can clear the entry.
    epmp_clear(12);
  } else {
    epmp_set_napot(12, kRvDmRegion, kEpmpPermLockedReadWriteExecute);
  }

  // ePMP region 13 gives read access to all of flash for both M and U modes.
  // This flash region was in ePMP region 5.
  epmp_set_napot(13, kFlashRegion, kEpmpPermLockedReadOnly);

  // Move the ROM_EXT virtual region from entry 6 to 10.
  uint32_t virtual_napot;
  CSR_READ(CSR_REG_PMPADDR6, &virtual_napot);
  epmp_clear(10);
  if (virtual_napot) {
    epmp_set_napot(10, epmp_decode_napot(virtual_napot),
                   kEpmpPermLockedReadOnly);
  }

  // Clear mutable ROM_EXT entries (8 & 9).
  epmp_clear(9);
  epmp_clear(8);

  // Immutable ROM_EXT TOR (6 & 7).
  epmp_set_tor(6, kImmTextRegion, kEpmpPermLockedReadExecute);

  // Clear entries from 5 ~ 3.
  epmp_clear(5);
  epmp_clear(4);
  epmp_clear(3);

  // 3 ~ 0 are ROM ePMP entries.
  // Leave them unchanged.

  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  return kErrorOk;
}

rom_error_t imm_section_epmp_mutable_rx(const manifest_t *manifest) {
  // Immutable ROM_EXT TOR (8 & 9).
  epmp_region_t mutable_code_region = manifest_code_region_get(manifest);

  // Manifest code_region includes immutable data segment. Move the start
  // address to exclude.
  mutable_code_region.start = (uintptr_t)_rom_ext_immutable_end;

  epmp_set_tor(8, mutable_code_region, kEpmpPermLockedReadExecute);

  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  return kErrorOk;
}
