// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ast.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"

enum {
  kBase = TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR,
};

rom_error_t ast_check(lifecycle_state_t lc_state) {
  // In some lifecycle states we want to continue the boot process even if the
  // AST is not initialized. Note that in these states OTP may not have been
  // configured.
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      return kErrorOk;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return kErrorOk;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      break;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      break;
    default:
      HARDENED_UNREACHABLE();
  }

  // OTP can be configured to skip AST initialization. In this situation we do
  // not check that AST_INIT_DONE is set.
  uint32_t en = otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET);
  if (launder32(en) == kMultiBitBool4False) {
    HARDENED_CHECK_EQ(en, kMultiBitBool4False);
    return kErrorOk;
  }

  // AST initialization may take up to 100us. It is most likely already complete
  // at this point but for resilience poll for up to 100us.
  // TODO: tune this timeout or use mcycle.
  for (int i = 0; i < 10000; ++i) {
    if (ast_init_done() == kHardenedBoolTrue) {
      HARDENED_CHECK_EQ(ast_init_done(), kHardenedBoolTrue);
      return kErrorOk;
    }
  }

  return kErrorAstInitNotDone;
}

static bool done_bit_get(void) {
  uint32_t reg = abs_mmio_read32(kBase + SENSOR_CTRL_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT);
}

hardened_bool_t ast_init_done(void) {
  static_assert(kHardenedBoolTrue == 0x739,
                "This function expects kHardenedBoolTrue to be 0x739");

  // The code below reads the AST_INIT_DONE bit twice and modifies `res` with
  // the result of each attempt. `res` should be `kHardenedBoolTrue` if all
  // attempts return true.
  hardened_bool_t res = 0x631;
  res |= done_bit_get() << 3;
  res |= done_bit_get() << 8;

  if (res != kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  return res;
}
