// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "hw/top/otp_ctrl_regs.h"
#include "hw/top/sram_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kSramCtrlBase = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR,
};

bool test_main(void) {
  uint32_t otp = otp_read32(
      OTP_CTRL_PARAM_CREATOR_SW_CFG_SRAM_KEY_RENEW_AND_INIT_EN_OFFSET);
  uint32_t status =
      abs_mmio_read32(kSramCtrlBase + SRAM_CTRL_STATUS_REG_OFFSET);
  bool key_valid = (status & (1 << SRAM_CTRL_STATUS_SCR_KEY_VALID_BIT)) != 0;

  LOG_INFO("sram_renew: otp=%x status=%x key_valid=%d", otp, status, key_valid);

  if (otp == kHardenedBoolFalse) {
    return !key_valid;
  } else {
    return key_valid;
  }
}
