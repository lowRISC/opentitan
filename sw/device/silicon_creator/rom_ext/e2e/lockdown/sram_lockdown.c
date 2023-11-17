// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

status_t test_sram_lockdown(void) {
  uint32_t exec, regwen;

  exec = abs_mmio_read32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                         SRAM_CTRL_EXEC_REG_OFFSET);
  regwen = abs_mmio_read32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REGWEN_REG_OFFSET);
  LOG_INFO("sram_exec = %x", exec);
  LOG_INFO("sram_exec_regwen = %x", regwen);
  if (exec != kMultiBitBool4False) {
    return UNKNOWN();
  }
  if (regwen != 0) {
    return UNKNOWN();
  }
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_sram_lockdown();
  if (status_err(sts)) {
    LOG_ERROR("sram_lockdown: %r", sts);
  }
  return status_ok(sts);
}
