// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include <assert.h>

#include "dt/dt_sram_ctrl.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"

#include "sram_ctrl_regs.h"  // Generated.

static const dt_sram_ctrl_t kSramCtrlDt = kDtSramCtrlRetAon;

void retention_sram_clear(void) {
  memset(retention_sram_get(), 0, sizeof(retention_sram_t));
}

void retention_sram_init(void) {
  uint32_t reg = bitfield_bit32_write(0, SRAM_CTRL_CTRL_INIT_BIT, true);
  uint32_t base = dt_sram_ctrl_primary_reg_block(kSramCtrlDt);
  abs_mmio_write32(base + SRAM_CTRL_CTRL_REG_OFFSET, reg);
}

void retention_sram_readback_enable(uint32_t en) {
  uint32_t base = dt_sram_ctrl_primary_reg_block(kSramCtrlDt);
  abs_mmio_write32(base + SRAM_CTRL_READBACK_REG_OFFSET, en);
}

void retention_sram_scramble(void) {
  // Request the renewal of the scrambling key and initialization to random
  // values.
  uint32_t ctrl = 0;
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_INIT_BIT, true);
  uint32_t base = dt_sram_ctrl_primary_reg_block(kSramCtrlDt);
  abs_mmio_write32(base + SRAM_CTRL_CTRL_REG_OFFSET, ctrl);
}

rom_error_t retention_sram_check_version(void) {
  retention_sram_t *rr = retention_sram_get();
  switch (rr->version) {
    case kRetentionSramVersion1:
      // Version 1 can be in-place upgraded to version 4.
      rr->version = kRetentionSramVersion4;
      break;
    case kRetentionSramVersion4:
      // Nothing to do for version 4.
      break;
    case kRetentionSramVersion3:
    case kRetentionSramVersion2:
    default:
      // Versions 2 and 3 never went into a product, so we should never see
      // them.  Other versions are not defined.
      return kErrorRetRamBadVersion;
  }
  return kErrorOk;
}

// Extern declarations for the inline functions in the header.
extern retention_sram_t *retention_sram_get(void);
