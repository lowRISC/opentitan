// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

static void aon_timer_test_wakeup_timer(dif_aon_timer_t *aon) {
  // Make sure that wake-up timer is stopped.
  CHECK(dif_aon_timer_wakeup_stop(aon) == kDifAonTimerOk);

  // Make sure the wake-up IRQ is cleared to avoid false positive.
  CHECK(dif_aon_timer_irq_acknowledge(aon, kDifAonTimerIrqWakeupThreshold) ==
        kDifAonTimerOk);
  bool is_pending;
  CHECK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWakeupThreshold,
                                     &is_pending) == kDifAonTimerOk);
  CHECK(!is_pending);

  // Test the wake-up timer functionality by setting a single cycle counter.
  // Delay to compensate for AON Timer 200kHz clock (less should suffice, but
  // to be on a cautious side - lets keep it at 100 for now).
  CHECK(dif_aon_timer_wakeup_start(aon, 1, 0) == kDifAonTimerOk);
  usleep(100);

  // Make sure that the timer has expired.
  CHECK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWakeupThreshold,
                                     &is_pending) == kDifAonTimerOk);
  CHECK(is_pending);

  CHECK(dif_aon_timer_wakeup_stop(aon) == kDifAonTimerOk);

  CHECK(dif_aon_timer_irq_acknowledge(aon, kDifAonTimerIrqWakeupThreshold) ==
        kDifAonTimerOk);
}

static void aon_timer_test_watchdog_timer(dif_aon_timer_t *aon) {
  // Make sure that watchdog timer is stopped.
  CHECK(dif_aon_timer_watchdog_stop(aon) == kDifAonTimerWatchdogOk);

  // Make sure the watchdog IRQ is cleared to avoid false positive.
  CHECK(dif_aon_timer_irq_acknowledge(
            aon, kDifAonTimerIrqWatchdogBarkThreshold) == kDifAonTimerOk);
  bool is_pending;
  CHECK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWatchdogBarkThreshold,
                                     &is_pending) == kDifAonTimerOk);
  CHECK(!is_pending);

  // Test the watchdog timer functionality by setting a single cycle "bark"
  // counter. Delay to compensate for AON Timer 200kHz clock (less should
  // suffice, but to be on a cautious side - lets keep it at 100 for now).
  CHECK(dif_aon_timer_watchdog_start(aon, 1, 0xffffffff, false, false) ==
        kDifAonTimerWatchdogOk);
  usleep(100);

  // Make sure that the timer has expired.
  CHECK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWatchdogBarkThreshold,
                                     &is_pending) == kDifAonTimerOk);
  CHECK(is_pending);

  CHECK(dif_aon_timer_watchdog_stop(aon) == kDifAonTimerWatchdogOk);

  CHECK(dif_aon_timer_irq_acknowledge(
            aon, kDifAonTimerIrqWatchdogBarkThreshold) == kDifAonTimerOk);
}

bool test_main(void) {
  dif_aon_timer_t aon;

  LOG_INFO("Running AON timer test");

  // Initialise AON Timer.
  dif_aon_timer_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
  };
  CHECK(dif_aon_timer_init(params, &aon) == kDifAonTimerOk);

  aon_timer_test_wakeup_timer(&aon);
  aon_timer_test_watchdog_timer(&aon);

  return true;
}
