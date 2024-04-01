// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include <assert.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"  // Generated.

enum {
  /**
   * Base address of retention SRAM control registers.
   */
  kBase = TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR,
};

static_assert(kRetentionSramBase == TOP_EARLGREY_RAM_RET_AON_BASE_ADDR,
              "Unexpected retention SRAM base address.");
static_assert(sizeof(retention_sram_t) == TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES,
              "Unexpected retention SRAM size.");

void retention_sram_clear(void) {
  memset(retention_sram_get(), 0, sizeof(retention_sram_t));
}

void retention_sram_init(void) {
  uint32_t reg = bitfield_bit32_write(0, SRAM_CTRL_CTRL_INIT_BIT, true);
  abs_mmio_write32(kBase + SRAM_CTRL_CTRL_REG_OFFSET, reg);
}

void retention_sram_scramble(void) {
  // Request the renewal of the scrambling key and initialization to random
  // values.
  uint32_t ctrl = 0;
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_INIT_BIT, true);
  abs_mmio_write32(kBase + SRAM_CTRL_CTRL_REG_OFFSET, ctrl);
}

rom_error_t retention_sram_check_version(void) {
  retention_sram_t *rr = retention_sram_get();
  switch (rr->version) {
    case kRetentionSramVersion1:
      // Version 1 can be in-place upgraded to version 3.
      rr->version = kRetentionSramVersion3;
      break;
    case kRetentionSramVersion3:
      // Nothing to do for version 3.
      break;
    case kRetentionSramVersion2:
    default:
      // Version 2 never went into a product, so we should never see it.
      // Other versions are not defined.
      return kErrorRetRamBadVersion;
  }
  return kErrorOk;
}

// Extern declarations for the inline functions in the header.
extern retention_sram_t *retention_sram_get(void);
