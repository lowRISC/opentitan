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

typedef struct test_scratchpad {
  uint32_t magic;
} test_scratchpad_t;

enum {
  kTestScratchPadMagic = 0x4e524653,  // "NRFS" (No Refresh)
};

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();
  test_scratchpad_t *scratch = (test_scratchpad_t *)retram->owner.reserved;

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    scratch->magic = kTestScratchPadMagic;
    LOG_INFO("Rebooting");
    rstmgr_reset();
    return false;
  }

  CHECK(scratch->magic == kTestScratchPadMagic,
        "Expected magic 0x%08x from previous boot, got 0x%08x (reboot not "
        "triggered by test)",
        kTestScratchPadMagic, scratch->magic);
  scratch->magic = 0;
  LOG_INFO("Rebooted");
  return true;
}
