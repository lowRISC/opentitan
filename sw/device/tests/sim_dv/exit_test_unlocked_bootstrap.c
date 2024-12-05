// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_lc_ctrl_t lc_ctrl;
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));

  dif_lc_ctrl_state_t state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &state));

  uint32_t rom_en = abs_mmio_read32(
      TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
      OTP_CTRL_PARAM_CREATOR_SW_CFG_ROM_EXEC_EN_OFFSET);

  if (rom_en == 0) {
    // The test should never reach here
    CHECK(false,
          "Unexpected branch - code not expected to execute since ROM "
          "execution is disabled");
  } else if (state == kDifLcCtrlStateProd && rom_en > 0) {
    // The test environment is waiting for this message
    LOG_INFO("ROM and flash execution successful");
    return true;
  }

  LOG_INFO("Current state is 0x%x, rom_en is 0x%x", state, rom_en);
  return false;
}
