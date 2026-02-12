// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/clkmgr.h"

#include "hw/top/dt/clkmgr.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/multibits.h"

#include "hw/top/clkmgr_regs.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'l', 'k')

hardened_bool_t clkmgr_check_jittery_clk_en(void) {
  uintptr_t clkmgr_base_addr = dt_clkmgr_primary_reg_block(kDtClkmgrAon);
  uint32_t jittery_clk_en =
      abs_mmio_read32(clkmgr_base_addr + CLKMGR_JITTER_ENABLE_REG_OFFSET);

  // Check that the jittery clock is set to kMultiBitBool4True
  if (launder32(jittery_clk_en) != kMultiBitBool4True) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(jittery_clk_en, kMultiBitBool4True);

  return kHardenedBoolTrue;
}
