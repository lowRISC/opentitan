// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/clkmgr.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "clkmgr_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'l', 'k')

enum {
  kBaseAddr = TOP_EARLGREY_CLKMGR_AON_BASE_ADDR,
};

hardened_bool_t clkmgr_check_jittery_clk_en(void) {
  uint32_t jittery_clk_en =
      abs_mmio_read32(kBaseAddr + CLKMGR_JITTER_ENABLE_REG_OFFSET);

  // Check that the jittery clock is set to kMultiBitBool4True
  if (launder32(jittery_clk_en) != kMultiBitBool4True) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(jittery_clk_en, kMultiBitBool4True);

  return kHardenedBoolTrue;
}
