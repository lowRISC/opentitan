// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
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
  1: adc_ctrl
  2: pinmux
  3: usb
  4: aon_timer
  5: sensor_ctrl

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

  // Enable access to flash for storing info across resets.
  LOG_INFO("Setting default region accesses");
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  uint32_t wakeup_count = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &wakeup_count));
  uint32_t wakeup_unit = get_wakeup_unit(wakeup_count);
  bool deep_sleep = get_deep_sleep(wakeup_count);

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("POR reset");
    execute_test(wakeup_unit, deep_sleep);
    check_wakeup_reason(wakeup_unit);
    LOG_INFO("Woke up by source %d", wakeup_unit);
    cleanup(wakeup_unit);
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_increment(&flash_ctrl, 0));
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &wakeup_count));
    wakeup_unit = get_wakeup_unit(wakeup_count);
    deep_sleep = get_deep_sleep(wakeup_count);
    delay_n_clear(4);
    execute_test(wakeup_unit, deep_sleep);
  } else {
    for (int i = 0; i < 2; ++i) {
      check_wakeup_reason(wakeup_unit);
      LOG_INFO("Woke up by source %d", wakeup_unit);
      cleanup(wakeup_unit);
      if (wakeup_unit == PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX &&
          deep_sleep) {
        return true;
      }
      CHECK_STATUS_OK(flash_ctrl_testutils_counter_increment(&flash_ctrl, 0));
      CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &wakeup_count));
      wakeup_unit = get_wakeup_unit(wakeup_count);
      deep_sleep = get_deep_sleep(wakeup_count);
      delay_n_clear(4);
      execute_test(wakeup_unit, deep_sleep);
    }
  }

  return false;
}
