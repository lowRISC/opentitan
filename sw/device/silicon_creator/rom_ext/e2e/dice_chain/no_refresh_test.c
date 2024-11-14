// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    LOG_INFO("Rebooting");
    rstmgr_reset();
    return false;
  }
  LOG_INFO("Rebooted");
  return true;
}
