// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rstmgr_regs.h"

// The reset reason value is really a bitfield. The power-on-reset indicator
// is defined by rstmgr_regs.h.
#define RESET_REASON_POR (1 << RSTMGR_RESET_INFO_POR_BIT)
// FIXME: I don't know where the HW_REQ field of the reset reason register
// is defined.  I observe a value of 2 for a watchdog reset.
#define RESET_REASON_WATCHDOG \
  ((2 << RSTMGR_RESET_INFO_HW_REQ_OFFSET) | RESET_REASON_POR)

void *const kRetentionRamBase = (void *)TOP_EARLGREY_RAM_RET_AON_BASE_ADDR;
const size_t kRetentionRamSize = TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES;

// Tests that we can pet the watchdog and avoid a reset.
rom_error_t watchdog_pet_test(void) {
  watchdog_init(500);
  for (size_t i = 0; i < 10; ++i) {
    LOG_INFO("watchdog = %x", watchdog_get());
    watchdog_pet();
    usleep(5000);
  }
  watchdog_init(0);
  return kErrorOk;
}

// Tests that if we neglect the dog, it will bite and reset the chip.
rom_error_t watchdog_bite_test(void) {
  watchdog_init(1);
  usleep(11000);
  watchdog_init(0);
  return kErrorUnknown;
}

const test_config_t kTestConfig;

// The test phases are tracked in retention RAM so that we ensure the reset
// happened in the correct phase of the test.
typedef enum TestPhase {
  kTestPhaseInit = 0,
  kTestPhasePet,
  kTestPhaseBite,
  kTestPhaseDone,
} test_phase_t;

bool test_main(void) {
  rom_error_t result = kErrorOk;
  uint32_t reason = rstmgr_reason_get();
  rstmgr_alert_info_enable();
  LOG_INFO("reset_info = %08x", reason);

  volatile test_phase_t *phase = (volatile test_phase_t *)kRetentionRamBase;
  if (reason == RESET_REASON_POR) {
    // Power-on: zero out the retention RAM.
    memset(kRetentionRamBase, 0, kRetentionRamSize);

    *phase = kTestPhasePet;
    EXECUTE_TEST(result, watchdog_pet_test);

    *phase = kTestPhaseBite;
    EXECUTE_TEST(result, watchdog_bite_test);
    // We should never get here - the escalate test should cause a reset
    // and we should see a reset reason of 0x11.
    *phase = kTestPhaseDone;
    LOG_ERROR("Test failure: should have reset before this line.");
  } else if (reason == RESET_REASON_WATCHDOG) {
    LOG_INFO("Detected reset after escalation test");
    if (*phase != kTestPhaseBite) {
      LOG_ERROR("Test failure: expected phase %d but got phase %d",
                kTestPhaseBite, *phase);
      result = kErrorUnknown;
    } else {
      result = kErrorOk;
    }
  } else {
    LOG_ERROR("Unknown reset reason");
    result = kErrorUnknown;
  }
  return result == kErrorOk;
}
