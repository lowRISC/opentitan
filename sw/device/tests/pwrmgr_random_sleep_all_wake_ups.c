// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/pwrmgr_sleep_all_wake_ups_impl.h"

/*
  PWRMGR RANDOM SLEEP ALL WAKE UPS TEST

  This test runs power manager wake up from normal or deep sleep mode by
  wake up inputs.

  For each wake up this tests normal and deep sleep in succession;
  for example, case 2 is adc_ctrl normal sleep and case 3 is adc_ctrl
  deep sleep.

  This is tracked by a retention sram counter, given there are resets involved.
 */

OTTF_DEFINE_TEST_CONFIG();

/**
 * Clean up pwrmgr wakeup reason register for the next round.
 */
static void delay_n_clear(uint32_t delay_in_us) {
  busy_spin_micros(delay_in_us);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

static uint32_t get_wakeup_unit(uint32_t count) { return count / 2; }

static bool get_deep_sleep(uint32_t count) { return (count % 2) == 1; }

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_units();

  ret_sram_testutils_init();

  uint32_t wakeup_count = 0;
  uint32_t wakeup_unit = 0;
  bool deep_sleep = false;
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

  if (wakeup_reason.request_sources == 0) {
    // This is a POR. Prepare to start the test.
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterCases));
  } else if (wakeup_reason.types != kDifPwrmgrWakeupTypeRequest) {
    LOG_ERROR("Unexpected wakeup_reason.types 0x%x", wakeup_reason.types);
    return false;
  } else {
    // This is a reset from deep_sleep wakeup. Run checks.
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterCases, &wakeup_count));
    wakeup_unit = get_wakeup_unit(wakeup_count);
    deep_sleep = get_deep_sleep(wakeup_count);
    CHECK(deep_sleep, "Should be deep sleep");
    check_wakeup_reason(wakeup_unit);
    LOG_INFO("Woke up by source %d", wakeup_unit);
    clear_wakeup(wakeup_unit);

    // All is well, get ready for the next test.
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterCases));
  }
  // All is well, get ready for the next unit, normal and deep sleep.
  while (true) {
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterCases, &wakeup_count));
    if (wakeup_count >= 2 * get_wakeup_count()) {
      return true;
    }
    wakeup_unit = get_wakeup_unit(wakeup_count);
    deep_sleep = get_deep_sleep(wakeup_count);
    delay_n_clear(4);
    CHECK(!deep_sleep, "Should be normal sleep");
    if (execute_test(wakeup_unit, deep_sleep)) {
      check_wakeup_reason(wakeup_unit);
      LOG_INFO("Woke up by source %d", wakeup_unit);
      clear_wakeup(wakeup_unit);
    }
    // Prepare deep sleep. The check is done above where a reset is handled.
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterCases));
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterCases, &wakeup_count));
    wakeup_unit = get_wakeup_unit(wakeup_count);
    deep_sleep = get_deep_sleep(wakeup_count);
    delay_n_clear(4);
    CHECK(deep_sleep, "Should be deep sleep");
    if (execute_test(wakeup_unit, deep_sleep)) {
      CHECK(false, "This is not reachable since we entered deep sleep");
    } else {
      // Increment test counter.
      CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterCases));
    }
  }

  // This is not reachable.
  return false;
}
