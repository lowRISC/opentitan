// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static_assert(kDtAonTimerCount >= 1,
              "This test requires at least one AON Timer instance");
static_assert(kDtRvCoreIbexCount >= 1,
              "This test requires at least one rv_core_ibex instance");

static const dt_aon_timer_t kTestAonTimer = (dt_aon_timer_t)0;
static const dt_rv_core_ibex_t kTestRvCoreIbex = (dt_rv_core_ibex_t)0;

OTTF_DEFINE_TEST_CONFIG();

static dif_aon_timer_t aon;
static dif_rv_core_ibex_t rv_core_ibex;
static volatile bool wdog_fired = false;

static void aon_timer_test_wakeup_timer(dif_aon_timer_t *aon) {
  // Test the wake-up timer functionality by setting a single cycle counter.
  // Delay to compensate for AON Timer 200kHz clock (less should suffice, but
  // to be on a cautious side - lets keep it at 100 for now).
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(aon, 1));

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

/**
 * OTTF external NMI internal IRQ handler.
 * The ROM configures the watchdog to generates a NMI at bark, so we clean the
 * NMI.
 */
void ottf_external_nmi_handler(void) {
  bool is_pending;
  // The watchdog bark external interrupt is also connected to the NMI input
  // of rv_core_ibex. We therefore expect the interrupt to be pending on the
  // peripheral side.
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(&aon, kDifAonTimerIrqWdogTimerBark,
                                            &is_pending));
  if (is_pending) {
    wdog_fired = true;
    CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon));
    // In order to handle the NMI we need to acknowledge the interrupt status
    // bit at the peripheral side.
    CHECK_DIF_OK(
        dif_aon_timer_irq_acknowledge(&aon, kDifAonTimerIrqWdogTimerBark));

    CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                  kDifRvCoreIbexNmiSourceWdog));
  }
}

static void aon_timer_test_watchdog_timer(dif_aon_timer_t *aon) {
  // Test the watchdog timer functionality by setting a single cycle "bark"
  // counter. Delay to compensate for AON Timer 200kHz clock (less should
  // suffice, but to be on a cautious side - lets keep it at 100 for now).
  CHECK_STATUS_OK(
      aon_timer_testutils_watchdog_config(aon, 1, UINT32_MAX, false));
  busy_spin_micros(100);

  dif_rv_core_ibex_nmi_state_t nmi_state;
  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(&rv_core_ibex, &nmi_state));

  // The TestROM does not enable NMI so we need to check that the IRQ was
  // requested.
  if (!nmi_state.wdog_enabled) {
    // Make sure that the timer has expired.
    bool is_pending;
    CHECK_DIF_OK(dif_aon_timer_irq_is_pending(aon, kDifAonTimerIrqWdogTimerBark,
                                              &is_pending));
    CHECK(is_pending);

    CHECK_DIF_OK(dif_aon_timer_watchdog_stop(aon));

    CHECK_DIF_OK(
        dif_aon_timer_irq_acknowledge(aon, kDifAonTimerIrqWdogTimerBark));
  } else {
    CHECK(wdog_fired);
  }
}

bool test_main(void) {
  LOG_INFO("Running AON timer test");

  // Initialise AON Timer.
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kTestAonTimer, &aon));
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kTestRvCoreIbex, &rv_core_ibex));

  aon_timer_test_wakeup_timer(&aon);
  aon_timer_test_watchdog_timer(&aon);

  return true;
}
