// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const dif_pwrmgr_wakeup_reason_t kWakeUpReasonTest = {
    .types = kDifPwrmgrWakeupTypeRequest,
    .request_sources = kDifPwrmgrWakeupRequestSourceFive,
};

static const dif_pwrmgr_wakeup_reason_t kWakeUpReasonPor = {
    .types = 0,
    .request_sources = 0,
};

const test_config_t kTestConfig;

bool compare_wakeup_reasons(const dif_pwrmgr_wakeup_reason_t *lhs,
                            const dif_pwrmgr_wakeup_reason_t *rhs) {
  return lhs->types == rhs->types &&
         lhs->request_sources == rhs->request_sources;
}

void aon_timer_wakeup_config(dif_aon_timer_t *aon_timer,
                             uint32_t wakeup_threshold) {
  // Make sure that wake-up timer is stopped.
  CHECK(dif_aon_timer_wakeup_stop(aon_timer) == kDifAonTimerOk);

  // Make sure the wake-up IRQ is cleared to avoid false positive.
  CHECK(dif_aon_timer_irq_acknowledge(
            aon_timer, kDifAonTimerIrqWakeupThreshold) == kDifAonTimerOk);

  bool is_pending;
  CHECK(dif_aon_timer_irq_is_pending(aon_timer, kDifAonTimerIrqWakeupThreshold,
                                     &is_pending) == kDifAonTimerOk);
  CHECK(!is_pending);

  CHECK(dif_aon_timer_wakeup_start(aon_timer, wakeup_threshold, 0) ==
        kDifAonTimerOk);
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_aon_timer_t aon_timer;

  // Initialize pwrmgr
  CHECK(dif_pwrmgr_init(
            (dif_pwrmgr_params_t){
                .base_addr =
                    mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR),
            },
            &pwrmgr) == kDifPwrmgrOk);

  // Assuming the chip hasn't slept yet, wakeup reason should be empty.
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason) == kDifPwrmgrOk);

  if (compare_wakeup_reasons(&wakeup_reason, &kWakeUpReasonPor)) {
    LOG_INFO("Powered up for the first time, begin test");

    // Initialize aon_timer
    dif_aon_timer_params_t params = {
        .base_addr =
            mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
    };
    CHECK(dif_aon_timer_init(params, &aon_timer) == kDifAonTimerOk);

    // Issue a wakeup singal in ~150us through the AON timer.
    //
    // At 200kHz, threshold of 30 is equal to 150us. There is an additional
    // ~4 cycle overhead for the CSR value to synchronize with the AON clock.
    // We should expect the wake up to trigger in ~170us. This is sufficient
    // time to allow pwrmgr config and the low power entry on WFI to complete.
    //
    // Adjust the threshold for Verilator since it runs on different clock
    // frequencies.
    uint32_t wakeup_threshold = 30;
    if (kDeviceType == kDeviceSimVerilator) {
      wakeup_threshold = 300;
    }
    aon_timer_wakeup_config(&aon_timer, wakeup_threshold);

    // Enable low power on the next WFI with default settings.
    // All clocks and power domains are turned off during low power.
    dif_pwrmgr_domain_config_t config;
    // Issue #6504: USB clock in active power must be left enabled.
    config = kDifPwrmgrDomainOptionUsbClockInActivePower;

    CHECK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeWakeup,
                                         kDifPwrmgrWakeupRequestSourceFive) ==
          kDifPwrmgrConfigOk);
    CHECK(dif_pwrmgr_set_domain_config(&pwrmgr, config) == kDifPwrmgrConfigOk);
    CHECK(dif_pwrmgr_low_power_set_enabled(&pwrmgr, kDifPwrmgrToggleEnabled) ==
          kDifPwrmgrConfigOk);

    // Enter low power mode.
    wait_for_interrupt();

  } else if (compare_wakeup_reasons(&wakeup_reason, &kWakeUpReasonTest)) {
    LOG_INFO("Aon timer wakeup detected");
    return true;

  } else {
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  return false;
}
