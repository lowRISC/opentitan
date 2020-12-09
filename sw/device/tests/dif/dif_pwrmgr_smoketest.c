// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_pwrmgr_t pwrmgr;
static dif_aon_timer_t aon_timer;

const test_config_t kTestConfig;
const dif_pwrmgr_wakeup_reason_t test_wakeup_reason = {
    .types = kDifPwrmgrWakeupTypeRequest,
    .request_sources = kDifPwrmgrWakeupRequestSourceFour,
};

const dif_pwrmgr_wakeup_reason_t por_wakeup_reason = {
    .types = 0,
    .request_sources = 0,
};

static bool compare_wakeup_reasons(const dif_pwrmgr_wakeup_reason_t *lhs,
                                   const dif_pwrmgr_wakeup_reason_t *rhs) {
  return lhs->types == rhs->types &&
         lhs->request_sources == rhs->request_sources;
}

static void aon_timer_setup(dif_aon_timer_t *aon) {
  // Make sure that wake-up timer is stopped.
  CHECK(dif_aon_timer_wakeup_stop(aon) == kDifAonTimerOk);

  // Make sure the wake-up IRQ is cleared to avoid false positive.
  CHECK(dif_aon_timer_irq_acknowledge(aon, kDifAonTimerIrqWakeupThreshold) ==
        kDifAonTimerOk);
  bool is_pending;
  CHECK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWakeupThreshold,
                                     &is_pending) == kDifAonTimerOk);
  CHECK(!is_pending);

  // Test the wake-up timer functionality by setting a small counter.
  // Delay to compensate for AON Timer 200kHz clock (less should suffice, but
  // to be on a cautious side - lets keep it at 100 for now).
  CHECK(dif_aon_timer_wakeup_start(aon, 5, 0) == kDifAonTimerOk);
  usleep(100);
}

bool test_main(void) {
  bool test_passed = false;

  // Initialize pwrmgr
  CHECK(dif_pwrmgr_init(
            (dif_pwrmgr_params_t){
                .base_addr =
                    mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR),
            },
            &pwrmgr) == kDifPwrmgrOk);

  // Initialize aon_timer
  dif_aon_timer_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
  };
  CHECK(dif_aon_timer_init(params, &aon_timer) == kDifAonTimerOk);

  // Assuming the chip hasn't slept yet, wakeup reason should be empty.
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason) == kDifPwrmgrOk);

  if (compare_wakeup_reasons(&wakeup_reason, &por_wakeup_reason)) {
    LOG_INFO("Powered up for the first time, begin test");
  } else if (compare_wakeup_reasons(&wakeup_reason, &test_wakeup_reason)) {
    test_passed = true;
    LOG_INFO("Aon timer wakeup detected");
  } else {
    CHECK(false);
  }

  if (!test_passed) {
    // setup aon timer wakeup
    aon_timer_setup(&aon_timer);

    // Enable low power on the next WFI with default settings.
    // All clocks and power domains are turned off during low power.
    dif_pwrmgr_domain_config_t config;
    config = 0;

    CHECK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeWakeup,
                                         kDifPwrmgrWakeupRequestSourceFour) ==
          kDifPwrmgrConfigOk);
    CHECK(dif_pwrmgr_set_domain_config(&pwrmgr, config) == kDifPwrmgrConfigOk);
    CHECK(dif_pwrmgr_low_power_set_enabled(&pwrmgr, kDifPwrmgrToggleEnabled) ==
          kDifPwrmgrConfigOk);

    // Enter low power mode.
    wait_for_interrupt();
  }

  return test_passed;
}
