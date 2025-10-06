// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/watchdog.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"

static uint32_t compute_ticks_per_ms(uint64_t hz) {
  const uint64_t kTicksPerMs = udiv64_slow(hz, 1000, NULL);
  CHECK(kTicksPerMs <= UINT32_MAX, "kTicksPerMs exceeds UINT32_MAX");
  return (uint32_t)kTicksPerMs;
}

// Setup the watchdog to bite.
static status_t watchdog_bite_setup(void) {
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
  return UNKNOWN();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  const retention_sram_t *rr = retention_sram_get();
  uint32_t reason = rr->creator.reset_reasons;

  if (bitfield_bit32_read(reason, kRstmgrReasonPowerOn)) {
    LOG_INFO("Configure watchdog to bite.");
    result = watchdog_bite_setup();
  } else if (bitfield_bit32_read(reason, kRstmgrReasonWatchdog)) {
    LOG_INFO("Got watchdog reset.");
    result = OK_STATUS();
  } else {
    LOG_ERROR("Unknown reset reason");
    result = UNKNOWN();
  }
  return status_ok(result);
}
