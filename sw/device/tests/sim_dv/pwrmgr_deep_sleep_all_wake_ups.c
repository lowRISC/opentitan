// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/sim_dv/pwrmgr_sleep_all_wake_ups_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/*
  PWRMGR DEEP SLEEP ALL WAKE UPS TEST

  This test runs power manager wake up from deep sleep mode by
  wake up inputs.

  There are 6 wake up inputs.
  0: sysrst_ctrl
  1: adc_ctrl
  2: pinmux
  3: usb
  4: aon_timer
  5: sensor_ctrl

  #5 is excluded because sensor_ctrl is not in the aon domain.
 */

#define PINMUX_WKUP_DETECTOR5 5

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

  init_units();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt.
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Enable access to flash for storing info across resets.
  LOG_INFO("Setting default region accesses");
  flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                             /*rd_en*/ true,
                                             /*prog_en*/ true,
                                             /*erase_en*/ true,
                                             /*scramble_en*/ false,
                                             /*ecc_en*/ false,
                                             /*he_en*/ false);

  uint32_t wakeup_count = flash_ctrl_testutils_counter_get(0);

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    LOG_INFO("POR reset");
    execute_test(wakeup_count, /*deep_sleep=*/true);
  } else {
    check_wakeup_reason(wakeup_count);
    LOG_INFO("Woke up by source %d", wakeup_count);
    cleanup(wakeup_count);
    if (wakeup_count == PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX) {
      return true;
    }
    flash_ctrl_testutils_counter_increment(&flash_ctrl, 0);
    delay_n_clear(4);
    execute_test(wakeup_count + 1, /*deep_sleep=*/true);
  }

  // Turn off the AON timer hardware completely before exiting.
  aon_timer_testutils_shutdown(&aon_timer);
  return false;
}
