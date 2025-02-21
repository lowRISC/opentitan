// Copyright lowRISC contributors (OpenTitan project).
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

#include "pwrmgr_regs.h"
#include "sensor_ctrl_regs.h"

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

 */

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_units();
  // Enable all AST alerts in sensor_ctrl

  // FIXME why is this needed in this test but not the random one?
  dif_sensor_ctrl_t sensor_ctrl;
  CHECK_DIF_OK(dif_sensor_ctrl_init_from_dt(kDtSensorCtrlAon, &sensor_ctrl));
  for (uint32_t k = 0; k < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; k++) {
    CHECK_DIF_OK(
        dif_sensor_ctrl_set_alert_en(&sensor_ctrl, k, kDifToggleEnabled));
  }

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0))) {
    LOG_INFO("POR reset");

    for (size_t wakeup_unit = 0; wakeup_unit < get_wakeup_count();
         ++wakeup_unit) {
      const test_wakeup_sources_t *src = get_wakeup_source(wakeup_unit, NULL);
      LOG_INFO("Test %d begin (%s)", wakeup_unit, src->name);
      execute_test(wakeup_unit, /*deep_sleep=*/false);
      check_wakeup_reason(wakeup_unit);
      LOG_INFO("Woke up by source %d", wakeup_unit);
      clear_wakeup(wakeup_unit);
      LOG_INFO("clean up done source %d", wakeup_unit);
    }
    return true;
  } else {
    LOG_ERROR("Unexpected wake up reason");
    return false;
  }
}
