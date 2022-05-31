// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

static void aon_timer_test_wakeup_timer(dif_aon_timer_t *aon) {
  // Test the wake-up timer functionality by setting a single cycle counter.
  // Delay to compensate for AON Timer 200kHz clock (less should suffice, but
  // to be on a cautious side - lets keep it at 100 for now).
  aon_timer_testutils_wakeup_config(aon, 1);

  busy_spin_micros(100);

  // Make sure that the timer has expired.
  bool is_pending;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon, kDifAonTimerIrqWkupTimerExpired, &is_pending));
  CHECK(is_pending);

  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(aon));

  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(aon, kDifAonTimerIrqWkupTimerExpired));
}

static void aon_timer_test_watchdog_timer(dif_aon_timer_t *aon) {
  // Test the watchdog timer functionality by setting a single cycle "bark"
  // counter. Delay to compensate for AON Timer 200kHz clock (less should
  // suffice, but to be on a cautious side - lets keep it at 100 for now).
  aon_timer_testutils_watchdog_config(aon, 1, UINT32_MAX, false);
  busy_spin_micros(100);

  // Make sure that the timer has expired.
  bool is_pending;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWdogTimerBark,
                                            &is_pending));
  CHECK(is_pending);

  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(aon));

  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(aon, kDifAonTimerIrqWdogTimerBark));
}

bool test_main(void) {
  dif_aon_timer_t aon;

  LOG_INFO("Running AON timer test");

  // Initialise AON Timer.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon));

  aon_timer_test_wakeup_timer(&aon);
  aon_timer_test_watchdog_timer(&aon);

  return true;
}
