// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/sim_dv/pwrmgr_sleep_all_wake_ups_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/*
  PWRMGR RANDOM SLEEP ALL WAKE UPS TEST

  This test runs power manager wake up from normal or deep sleep mode by
  wake up inputs.

  There are 6 wake up inputs.
  0: sysrst_ctrl
  1: adc_ctrl, only runnable in DV
  2: pinmux
  3: usb
  4: aon_timer
  5: sensor_ctrl

  #1 is excluded in non-DV because it forces an internal signal.
  #5 is excluded because sensor_ctrl is not in the aon domain.

  There are 10 cases to be tested. For each wake up this tests the normal and
  deep sleep in succession; for example, case 2 is adc_ctrl normal sleep and
  case 3 is adc_ctrl deep sleep.

  This is tracked by a flash_ctrl counter, given there are resets involved.
 */

OTTF_DEFINE_TEST_CONFIG();

/**
 * Clean up pwrmgr wakeup reason register for the next round.
 */
static void delay_n_clear(uint32_t delay_in_us) {
  busy_spin_micros(delay_in_us);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

uint32_t get_wakeup_unit(uint32_t count) { return count / 2; }

bool get_deep_sleep(uint32_t count) { return (count % 2) == 1; }

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_units();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt.
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
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
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterCases, &wakeup_count));

    // Check if all wakeups are tested, or some need to be skipped.
    if (wakeup_count >= 2 * PWRMGR_PARAM_NUM_WKUPS) {
      return true;
    } else if (kDeviceType != kDeviceSimDV &&
               wakeup_count == 2 * PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX) {
      // Skip both normal and deep sleep.
      wakeup_count += 2;
      CHECK_STATUS_OK(
          ret_sram_testutils_counter_set(kCounterCases, wakeup_count));
    }
  }
  // All is well, get ready for the next unit, normal and deep sleep.
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterCases, &wakeup_count));
  wakeup_unit = get_wakeup_unit(wakeup_count);
  deep_sleep = get_deep_sleep(wakeup_count);
  delay_n_clear(4);
  CHECK(!deep_sleep, "Should be normal sleep");
  execute_test(wakeup_unit, deep_sleep);
  check_wakeup_reason(wakeup_unit);
  LOG_INFO("Woke up by source %d", wakeup_unit);
  clear_wakeup(wakeup_unit);
  // Prepare deep sleep. The check is done above where a reset is handled.
  CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterCases));
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterCases, &wakeup_count));
  wakeup_unit = get_wakeup_unit(wakeup_count);
  deep_sleep = get_deep_sleep(wakeup_count);
  delay_n_clear(4);
  CHECK(deep_sleep, "Should be deep sleep");
  execute_test(wakeup_unit, deep_sleep);

  // This is not reachable.
  return false;
}
