// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/pwrmgr_sleep_all_wake_ups_impl.h"

/*
  PWRMGR NORMAL SLEEP ALL WAKE UPS test

  This test runs power manager wake up from deep sleep mode by
  wake up inputs.
 */

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_units();

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0))) {
    LOG_INFO("POR reset");

    for (size_t wakeup_unit = 0; wakeup_unit < get_wakeup_count();
         ++wakeup_unit) {
      if (!execute_test(wakeup_unit, /*deep_sleep=*/false)) {
        continue;
      }
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
