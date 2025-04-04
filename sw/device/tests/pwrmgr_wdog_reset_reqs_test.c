// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static_assert(kDtPwrmgrCount == 1, "this test expects exactly one pwrmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects exactly one rstmgr");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtAonTimerCount >= 1,
              "this test expects at least one aon_timer");
static const dt_aon_timer_t kAonTimerDt = 0;

OTTF_DEFINE_TEST_CONFIG();

/**
 * Configure the wdog.
 */
static void config_wdog(const dif_aon_timer_t *aon_timer,
                        const dif_pwrmgr_t *pwrmgr, uint64_t bark_time_us,
                        uint64_t bite_time_us) {
  uint32_t bark_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(bark_time_us,
                                                                &bark_cycles));
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(bite_time_us,
                                                                &bite_cycles));

  LOG_INFO("Wdog will bark after %u us and bite after %u us",
           (uint32_t)bark_time_us, (uint32_t)bite_time_us);

  // Set wdog as a reset source.
  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      pwrmgr, kDifPwrmgrReqTypeReset, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerResetReqAonTimer, &reset_sources));
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));

  // Setup the wdog bark and bite timeouts.
  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(aon_timer, bark_cycles,
                                                      bite_cycles, false));
}

/**
 * Execute the aon timer wdog bite reset test.
 */
static void wdog_bite_test(const dif_aon_timer_t *aon_timer,
                           const dif_pwrmgr_t *pwrmgr, uint32_t bark_time_us) {
  uint64_t bite_time_us = bark_time_us * 2;
  config_wdog(aon_timer, pwrmgr, bark_time_us, bite_time_us);

  // The `intr_state` takes 3 aon clock cycles to rise plus 2 extra cycles as a
  // precaution.
  uint64_t aon_timer_clock_freq_hz = dt_clock_frequency(
      dt_aon_timer_clock(kDtAonTimerAon, kDtAonTimerClockAon));
  uint32_t wait_us =
      (uint32_t)bark_time_us +
      (uint32_t)udiv64_slow(5 * 1000000 + aon_timer_clock_freq_hz - 1,
                            aon_timer_clock_freq_hz, NULL);

  // Wait bark time and check that the bark interrupt requested.
  busy_spin_micros(wait_us);
  bool is_pending = false;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  CHECK(is_pending, "Wdog bark irq did not rise after %u microseconds",
        wait_us);

  // Wait for the remaining time to the wdog bite.
  busy_spin_micros(wait_us);
  // If we arrive here the test must fail.
  CHECK(false, "Timeout waiting for Wdog bite reset!");
}

bool test_main(void) {
  // Initialize pwrmgr.
  dif_pwrmgr_t pwrmgr;
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  // Initialize rstmgr to check the reset reason.
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));

  // Initialize aon timer to use the wdog.
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));

  // Check if there was a HW reset caused by the wdog bite.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoWatchdog,
        "Wrong reset reason %02X", rst_info);

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, setting wdog");
    // Executing the wdog bite reset test.
    wdog_bite_test(&aon_timer, &pwrmgr, /*bark_time_us=*/200);
  } else if (rst_info == kDifRstmgrResetInfoWatchdog) {
    LOG_INFO("Booting for the second time due to wdog bite reset");

    return true;
  }
  LOG_ERROR("Got unexpected reset info 0x%x", rst_info);
  return false;
}
