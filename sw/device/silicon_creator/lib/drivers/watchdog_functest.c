// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rstmgr_regs.h"

static uint32_t compute_ticks_per_ms(uint64_t hz) {
  const uint64_t kTicksPerMs = udiv64_slow(hz, 1000, NULL);
  CHECK(kTicksPerMs <= UINT32_MAX, "kTicksPerMs exceeds UINT32_MAX");
  return (uint32_t)kTicksPerMs;
}

// Tests that we can pet the watchdog and avoid a reset.
static rom_error_t watchdog_pet_test(void) {
  // Set watchdog bite threshold to 5ms.
  uint32_t bite_threshold = 5 * compute_ticks_per_ms(kClockFreqAonHz);
  uint32_t bark_threshold = 9 * bite_threshold / 8;
  LOG_INFO("bite threshold = %d", bite_threshold);
  LOG_INFO("bark threshold = %d", bark_threshold);
  watchdog_configure((watchdog_config_t){
      .bite_threshold = bite_threshold,
      .bark_threshold = bark_threshold,
      .enable = kHardenedBoolTrue,
  });

  for (size_t i = 0; i < 10; ++i) {
    watchdog_pet();

    // Sleep for 1ms.
    busy_spin_micros(1 * 1000);
  }
  watchdog_disable();
  return kErrorOk;
}

// Tests that we can configure the watchdog in a disabled state.
static rom_error_t watchdog_configure_disabled_test(void) {
  // Set watchdog bite threshold to 1ms.
  uint32_t threshold = 1 * compute_ticks_per_ms(kClockFreqAonHz);
  LOG_INFO("threshold = %d", threshold);
  watchdog_configure((watchdog_config_t){
      .bite_threshold = threshold,
      .bark_threshold = threshold,
      .enable = kHardenedBoolFalse,
  });

  // Sleep for 5ms.
  busy_spin_micros(5 * 1000);
  return kErrorOk;
}

// Tests that if we neglect the dog, it will bite and reset the chip.
static rom_error_t watchdog_bite_test(void) {
  // Set watchdog bite threshold to 5ms.
  uint32_t bite_threshold = 5 * compute_ticks_per_ms(kClockFreqAonHz);
  uint32_t bark_threshold = 9 * bite_threshold / 8;
  LOG_INFO("bite threshold = %d", bite_threshold);
  LOG_INFO("bark threshold = %d", bark_threshold);
  watchdog_configure((watchdog_config_t){
      .bite_threshold = bite_threshold,
      .bark_threshold = bark_threshold,
      .enable = kHardenedBoolTrue,
  });

  // Sleep for 6ms.
  busy_spin_micros(6 * 1000);

  watchdog_disable();
  return kErrorUnknown;
}

OTTF_DEFINE_TEST_CONFIG();

// The test phases are tracked in retention RAM so that we ensure the reset
// happened in the correct phase of the test.
typedef enum TestPhase {
  kTestPhaseInit = 0,
  kTestPhasePet,
  kTestPhaseDisable,
  kTestPhaseBite,
  kTestPhaseDone,
} test_phase_t;

bool test_main(void) {
  status_t result = OK_STATUS();
  uint32_t reason = rstmgr_testutils_reason_get();
  rstmgr_alert_info_enable();
  LOG_INFO("reset_info = %08x", reason);

  // Clear the existing reset reason(s) so that they do not appear after the
  // next reset.
  rstmgr_testutils_reason_clear();

  // Use the part of the retention SRAM reserved for the silicon owner to
  // store the test phase.
  uint32_t *phase = &retention_sram_get()->reserved_owner[0];

  if (bitfield_bit32_read(reason, kRstmgrReasonPowerOn)) {
    sec_mmio_init();

    // Power-on: zero out the retention RAM.
    retention_sram_clear();

    *phase = kTestPhasePet;
    EXECUTE_TEST(result, watchdog_pet_test);

    *phase = kTestPhaseDisable;
    EXECUTE_TEST(result, watchdog_configure_disabled_test);

    *phase = kTestPhaseBite;
    EXECUTE_TEST(result, watchdog_bite_test);

    *phase = kTestPhaseDone;
    LOG_ERROR("Test failure: should have reset before this line.");
  } else if (bitfield_bit32_read(reason, kRstmgrReasonWatchdog)) {
    LOG_INFO("Detected reset after escalation test");
    if (*phase != kTestPhaseBite) {
      LOG_ERROR("Test failure: expected phase %d but got phase %d",
                kTestPhaseBite, *phase);
      result = UNKNOWN();
    } else {
      result = OK_STATUS();
    }
  } else {
    LOG_ERROR("Unknown reset reason");
    result = UNKNOWN();
  }
  return status_ok(result);
}
