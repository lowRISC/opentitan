// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"  // Generated.

enum {
  /**
   * Base address of retention SRAM controller.
   */
  kBase = TOP_EARLGREY_SRAM_CTRL_RET_AON_BASE_ADDR,
};

rom_error_t retention_sram_scramble(void) {
  // Check that control register writes are enabled.
  if (!bitfield_bit32_read(
          abs_mmio_read32(kBase + SRAM_CTRL_CTRL_REGWEN_REG_OFFSET),
          SRAM_CTRL_CTRL_REGWEN_CTRL_REGWEN_BIT)) {
    return kErrorRetSramLocked;
  }

  // Request the renewal of the scrambling key and initialization to random
  // values.
  uint32_t ctrl = 0;
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT, true);
  ctrl = bitfield_bit32_write(ctrl, SRAM_CTRL_CTRL_INIT_BIT, true);
  abs_mmio_write32(kBase + SRAM_CTRL_CTRL_REG_OFFSET, ctrl);

  return kErrorOk;
}
