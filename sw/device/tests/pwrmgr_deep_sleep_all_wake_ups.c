// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/pwrmgr_sleep_all_wake_ups_impl.h"

/*
  PWRMGR DEEP SLEEP ALL WAKE UPS TEST

  This test runs power manager wake up from deep sleep mode by
  wake up inputs.
 */

OTTF_DEFINE_TEST_CONFIG();

/**
 * Clean up pwrmgr wakeup reason register for the next round.
 */
static void delay_n_clear(uint32_t delay_in_us) {
  busy_spin_micros(delay_in_us);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  ret_sram_testutils_init();

  init_units();

  uint32_t wakeup_unit = 0;

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0))) {
    LOG_INFO("POR reset");
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterCases));
  } else {
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterCases, &wakeup_unit));
    check_wakeup_reason(wakeup_unit);
    LOG_INFO("Woke up by source %d", wakeup_unit);
    clear_wakeup(wakeup_unit);
    delay_n_clear(4);
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterCases));
  }

  while (true) {
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterCases, &wakeup_unit));
    if (wakeup_unit >= get_wakeup_count()) {
      return true;
    }
    if (execute_test(wakeup_unit, /*deep_sleep=*/true)) {
      CHECK(false, "This is not reachable since we entered deep sleep");
    } else {
      // Skip test.
      CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterCases));
    }
  }

  return false;
}
