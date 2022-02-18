// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/freestanding/limits.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define WDOG_BARK_TIME (5 * 1000)  // 5ms
const test_config_t kTestConfig;

/**
 * Configure the wdog.
 */
static void config_wdog(const dif_aon_timer_t *aon_timer,
                        const dif_pwrmgr_t *pwrmgr, uint64_t bark_time_us,
                        uint64_t bite_time_us) {
  uint64_t bark_cycles = (bark_time_us * kClockFreqAonHz / 1000000);
  uint64_t bite_cycles = (bite_time_us * kClockFreqAonHz / 1000000);

  CHECK(bite_cycles < UINT32_MAX,
        "The value %u can't fit into the 32 bits timer counter.", bite_cycles);

  LOG_INFO("Wdog will bark after %u us and bite after %u us",
           (uint32_t)bark_time_us, (uint32_t)bite_time_us);

  // Set wdog as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));

  // Setup the wdog bark and bite timeouts.
  aon_timer_testutils_watchdog_config(aon_timer, bark_cycles, bite_cycles,
                                      false);
}

/**
 * Execute the aon timer wdog bite reset test.
 */
static void wdog_bite_test(const dif_aon_timer_t *aon_timer,
                           const dif_pwrmgr_t *pwrmgr, uint64_t bark_time_us) {
  uint64_t bite_time_us = bark_time_us * 2;
  config_wdog(aon_timer, pwrmgr, bark_time_us, bite_time_us);

  // Wait bark time and check that the bark interrupt requested.
  busy_spin_micros(bark_time_us);
  bool is_pending = false;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  CHECK(is_pending);

  // Wait for the remaining time to the wdog bite.
  busy_spin_micros(bite_time_us - bark_time_us);
  // If we arrive here the test must fail.
  CHECK(false, "Timeout waiting for Wdog bite reset!");
}

/**
 * Execute the aon timer wdog bite reset during sleep test.
 */
static void sleep_wdog_bite_test(const dif_aon_timer_t *aon_timer,
                                 const dif_pwrmgr_t *pwrmgr,
                                 uint64_t bark_time_us) {
  uint64_t bite_time_us = bark_time_us * 2;
  config_wdog(aon_timer, pwrmgr, bark_time_us, bite_time_us);

  // Program the pwrmgr to go to deep sleep state (clocks off).
  pwrmgr_testutils_enable_low_power(pwrmgr, kDifPwrmgrWakeupRequestSourceTwo,
                                    0);
  // Enter in low power mode.
  wait_for_interrupt();
  // If we arrive here the test must fail.
  CHECK(false, "Fail to enter in low power mode!");
}

bool test_main(void) {
  // Initialize pwrmgr.
  dif_pwrmgr_t pwrmgr;
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize rstmgr to check the reset reason.
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Initialize aon timer to use the wdog.
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  // Check if there was a HW reset caused by the wdog bite.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &rst_info));
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoWatchdog ||
            rst_info ==
                (kDifRstmgrResetInfoWatchdog | kDifRstmgrResetInfoLowPowerExit),
        "Wrong reset reason %02X", rst_info);

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, setting wdog");
    // Executing the wdog bite reset test.
    wdog_bite_test(&aon_timer, &pwrmgr, WDOG_BARK_TIME);
  } else if (rst_info == kDifRstmgrResetInfoWatchdog) {
    LOG_INFO("Booting for the second time due to wdog bite reset");
    // Executing the wdog bite reset during sleep test.
    sleep_wdog_bite_test(&aon_timer, &pwrmgr, WDOG_BARK_TIME);
  } else if (rst_info ==
             (kDifRstmgrResetInfoWatchdog | kDifRstmgrResetInfoLowPowerExit)) {
    LOG_INFO("Booting for the tird time due to wdog bite reset during sleep");
  }

  return true;
}
