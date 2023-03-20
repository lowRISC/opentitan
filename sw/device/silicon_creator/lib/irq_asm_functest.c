// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Exception handler written in assembly.
 *
 * Resets the device using the watchdog timer. Does not return.
 */
extern noreturn void _asm_exception_handler(void);

OTTF_DEFINE_TEST_CONFIG();

// The test phases are tracked in retention RAM so that we ensure the reset
// happened in the correct phase of the test.
typedef enum TestPhase {
  kTestPhaseInit = 0,
  kTestPhaseReset = 1,
  kTestPhaseDone = 2,
} test_phase_t;

bool test_main(void) {
  uint32_t reason = rstmgr_testutils_reason_get();
  LOG_INFO("reset_info = %08x", reason);

  // Clear the existing reset reason(s) so that they do not appear after the
  // next reset.
  rstmgr_testutils_reason_clear();

  // Use the part of the retention SRAM reserved for the silicon owner to
  // store the test phase.
  uint32_t *phase = &retention_sram_get()->reserved_owner[0];

  if (bitfield_bit32_read(reason, kRstmgrReasonPowerOn)) {
    // First execution after bootstrap: Zero out the retention RAM.
    retention_sram_clear();

    LOG_INFO("Calling exception handler to reset device.");
    *phase = kTestPhaseReset;
    _asm_exception_handler();

    CHECK(false);  // Unreachable.
  } else if (bitfield_bit32_read(reason, kRstmgrReasonSoftwareRequest)) {
    // Software reset: check that the test phase is correct.
    CHECK(bitfield_popcount32(reason) == 1, "Expected exactly 1 reset reason.");
    LOG_INFO("Detected reset after exception test");
    if (*phase != kTestPhaseReset) {
      LOG_ERROR("Test failure: expected phase %d but got phase %d",
                kTestPhaseReset, *phase);
    } else {
      return true;  // Pass.
    }
  } else {
    LOG_ERROR("Unknown reset reason");
  }
  return false;  // Fail.
}
