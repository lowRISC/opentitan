// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "sram_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kSramCtrlBase = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR,
};

bool test_main(void) {
  uint32_t otp =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_SRAM_READBACK_EN_OFFSET);
  uint32_t cfg = abs_mmio_read32(kSramCtrlBase + SRAM_CTRL_READBACK_REG_OFFSET);
  LOG_INFO("sram_readback: otp=%x cfg=%x", otp, cfg);
  return otp == cfg;
}
