// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/sim_dv/pwrmgr_sleep_all_wake_ups_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

/*
  PWRMGR NORMAL SLEEP ALL WAKE UPS test

  This test runs power manager wake up from deep sleep mode by
  wake up inputs.

  There are 6 wake up inputs.
  0: sysrst_ctrl
  1: adc_ctrl
  2: pinmux
  3: usb
  4: aon_timer
  5: sensor_ctrl

#define PWRMGR_PARAM_NUM_WKUPS 6

#define PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX 0
#define PWRMGR_PARAM_ADC_CTRL_AON_WKUP_REQ_IDX 1
#define PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX 2
#define PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX 3
#define PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX 4
#define PWRMGR_PARAM_SENSOR_CTRL_WKUP_REQ_IDX 5

 */

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kPinmuxWkupDetector5 = 5;

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_units();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    LOG_INFO("POR reset");

    for (size_t i = 0; i < PWRMGR_PARAM_NUM_WKUPS; ++i) {
      LOG_INFO("Test %d begin", i);
      execute_test(i, /*deep_sleep=*/false);
      check_wakeup_reason(i);
      LOG_INFO("Woke up by source %d", i);
      cleanup(i);
      LOG_INFO("clean up done source %d", i);
    }

    // Turn off the AON timer hardware completely before exiting.
    aon_timer_testutils_shutdown(&aon_timer);
    return true;
  }

  return false;
}
