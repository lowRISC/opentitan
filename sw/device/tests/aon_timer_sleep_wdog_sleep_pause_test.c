// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

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

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this library expects exactly one pwrmgr");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this library expects exactly one rstmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount == 1,
              "this library expects exactly one aon_timer");

#define IDLE_TIME_US 10
#define WKUP_TIME_US 2000
OTTF_DEFINE_TEST_CONFIG();

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

  // Find wakeup and reset sources.
  dif_pwrmgr_request_sources_t wakeup_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerWakeupWkupReq, &wakeup_sources));
  dif_pwrmgr_request_sources_t reset_sources;
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeReset, dt_aon_timer_instance_id(kAonTimerDt),
      kDtAonTimerResetReqAonTimer, &reset_sources));

  // Enable aon_timer watchdog reset.
  // Set wdog as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeReset, reset_sources, kDifToggleEnabled));

  // Check if there was a HW reset caused by the wdog bite.
  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  uint64_t wkup_cnt;
  uint32_t wdog_cnt;
  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, setting wdog");

    // Configure watchdog sooner then wakeup, but with pause enabled.
    uint64_t wkup_cycles = 0;
    CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_64_from_us(
        WKUP_TIME_US, &wkup_cycles));

    // The actual expiration of the watchdog is unimportant, as the test
    // mainly checks the count.
    CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(&aon_timer, UINT32_MAX,
                                                        UINT32_MAX, true));
    CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(&aon_timer, wkup_cycles));

    busy_spin_micros(IDLE_TIME_US);

    // Since watchdog was started first, its count should be larger.
    CHECK_DIF_OK(dif_aon_timer_watchdog_get_count(&aon_timer, &wdog_cnt));
    CHECK_DIF_OK(dif_aon_timer_wakeup_get_count(&aon_timer, &wkup_cnt));
    CHECK(wdog_cnt >= wkup_cnt);

    // Deep sleep.
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources,
                                                      /*domain_config=*/0));

    // Enter low power mode.
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();
  } else if (rst_info == kDifRstmgrResetInfoLowPowerExit) {
    LOG_INFO("Booting for the second time due to wakeup");
    // Since watchdog count was paused during low power, wakeup
    // count should now be larger.
    CHECK_DIF_OK(dif_aon_timer_wakeup_get_count(&aon_timer, &wkup_cnt));
    CHECK_DIF_OK(dif_aon_timer_watchdog_get_count(&aon_timer, &wdog_cnt));
    CHECK(wdog_cnt < wkup_cnt);

  } else {
    LOG_ERROR("Got unexpected reset_info=0x%x", rst_info);
  }

  return true;
}
