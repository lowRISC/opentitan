// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_aon_timer.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this test expects a rstmgr");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");

// When the test first runs the rstmgr's `reset_info` CSR should have the POR
// bit set, the code clears reset_info and puts the chip in shallow sleep. WFI
// causes core_sleeping to rise, and that causes the SV side to glitch the main
// power rail, causing a pwrmgr internally generated reset. The next time the
// test runs is after the power glitch reset, which is confirmed reading the
// `reset_info` CSR.
bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  // Initialize pwrmgr since this will put the chip in shallow sleep.
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  // Initialize rstmgr since this will check some registers.
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));

  // Notice we are clearing rstmgr's RESET_INFO, so after the power glitch there
  // is only one bit set.

  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    LOG_INFO("Powered up for the first time, begin test");

    CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true);

    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

    // Configure shallow sleep.
    dif_pwrmgr_request_sources_t wakeup_sources;
    CHECK_DIF_OK(dif_pwrmgr_find_request_source(
        &pwrmgr, kDifPwrmgrReqTypeWakeup,
        dt_aon_timer_instance_id(kDtAonTimerAon), kDtAonTimerWakeupWkupReq,
        &wakeup_sources));

    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, wakeup_sources, kDifPwrmgrDomainOptionMainPowerInLowPower));

    // This causes core_sleeping to rise and triggers the injection of the
    // power glitch. Enter shallow sleep mode.
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();

  } else {
    LOG_INFO("Checking reset status.");
    LOG_INFO("EXP: 0x%x", (kDifRstmgrResetInfoPowerUnstable));
    CHECK_STATUS_OK(rstmgr_testutils_post_reset(
        &rstmgr, kDifRstmgrResetInfoPowerUnstable, 0, 0, 0, 0));
    LOG_INFO(
        "Reset status indicates a main power glitch and low power exit reset");
  }
  return true;
}
