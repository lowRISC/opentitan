// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Test phases tracked in retention RAM.
 */
enum {
  kTestPhaseInit = 0,
  kTestPhaseReset = 1,
  kTestPhaseDone = 2,
};

bool test_main(void) {
  // Read and clear reset reason.
  uint32_t reason = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  LOG_INFO("Reset reason: 0x%08x", reason);
  // This test assumes that reset reason is unique.
  CHECK(bitfield_popcount32(reason) == 1, "Expected exactly 1 reset reason.");

  // Use the part of the retention RAM reserved for the silicon owner to store
  // the test phase.
  uint32_t *phase = &retention_sram_get()->reserved_owner[0];

  if (bitfield_bit32_read(reason, kRstmgrReasonPowerOn)) {
    // Clear retention RAM on power-on reset.
    retention_sram_clear();
    // Request a system reset.
    *phase = kTestPhaseReset;
    rstmgr_reset();
    CHECK(false, "Should have reset before this line.");  // Unreachable
  } else if (bitfield_bit32_read(reason, kRstmgrReasonSoftwareRequest)) {
    LOG_INFO("Detected software reset.");
    CHECK(*phase == kTestPhaseReset, "Unexpected test phase: 0x%08x", *phase);
    *phase = kTestPhaseDone;
    return true;
  }
  LOG_ERROR("Unknown reset reason: 0x%08x", reason);
  return false;
}
