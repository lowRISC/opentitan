// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "pwrmgr_regs.h"

enum {
  kPlicTarget = 0,
};

static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t rv_plic;
static dif_aon_timer_t timer;

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_aon_timer_t kAonTimerDt = 0;
static_assert(kDtAonTimerCount == 1, "this test expects an aon_timer");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects exactly one rv_plic");

static dif_pwrmgr_request_sources_t wakeup_src;

bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_aon_timer_instance_id(kAonTimerDt)) {
    LOG_INFO("AON Timer ISR");
    dif_aon_timer_irq_t irq =
        dt_aon_timer_irq_from_plic_id(kAonTimerDt, irq_id);

    if (irq == kDtAonTimerIrqWkupTimerExpired) {
      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&timer));
    } else if (irq == kDtAonTimerIrqWdogTimerBark) {
      CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&timer));
    }
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&timer, irq));
    bool is_pending = true;
    CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
        &timer, kDifAonTimerIrqWkupTimerExpired, &is_pending));
    CHECK(!is_pending);
    return true;
  } else if (devid == dt_pwrmgr_instance_id(kPwrmgrDt)) {
    LOG_INFO("Pwrmgr ISR");
    CHECK(irq_id == dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup),
          "Pwrmgr IRQ ID: %d is incorrect", irq_id);
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));
    return true;
  } else {
    return false;
  }
}

static bool get_wakeup_status(void) {
  dif_pwrmgr_request_sources_t wake_req = ~0u;
  CHECK_DIF_OK(dif_pwrmgr_get_current_request_sources(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, &wake_req));
  return (wake_req > 0);
}

static void clear_wakeup(void) {
  CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&timer));
  // Ensure the de-asserted events have cleared from the wakeup pipeline
  // within 100us.
  IBEX_SPIN_FOR(!get_wakeup_status(), 100);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

static void test_init(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));

  CHECK_DIF_OK(
      dif_pwrmgr_find_request_source(&pwrmgr, kDifPwrmgrReqTypeWakeup,
                                     dt_aon_timer_instance_id(kDtAonTimerAon),
                                     kDtAonTimerWakeupWkupReq, &wakeup_src));

  // Enable AON interrupts.
  dif_rv_plic_irq_id_t plic_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&rv_plic, kPlicTarget, plic_id, plic_id);
  rv_plic_testutils_irq_range_enable(
      &rv_plic, kPlicTarget,
      dt_aon_timer_irq_to_plic_id(kAonTimerDt, kDtAonTimerIrqWkupTimerExpired),
      dt_aon_timer_irq_to_plic_id(kAonTimerDt, kDtAonTimerIrqWdogTimerBark));

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &timer));
  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&timer));
}

static void set_timer(uint64_t time) {
  uint32_t cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(time, &cycles));
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(&timer, cycles));
}

static bool lowpower_hint_is_cleared(void) {
  dif_toggle_t low_power_enabled = kDifToggleEnabled;
  CHECK_DIF_OK(dif_pwrmgr_low_power_get_enabled(&pwrmgr, &low_power_enabled));
  return low_power_enabled == kDifToggleDisabled;
}

static void test_sleep(bool wfi_fallthrough) {
  LOG_INFO("Low power WFI (fallthrough=%d)", wfi_fallthrough);

  dif_pwrmgr_domain_config_t domain_config =
      kDifPwrmgrDomainOptionMainPowerInLowPower;
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_src, domain_config));
  irq_global_ctrl(false);
  if (wfi_fallthrough) {
    LOG_INFO("Fallthough WFI due to timer pending");
    set_timer(100);
    busy_spin_micros(200);
  } else {
    set_timer(100);
  }
  wait_for_interrupt();
  LOG_INFO("Woke up by source %x", wakeup_src);
  CHECK_DIF_OK(dif_pwrmgr_low_power_set_enabled(&pwrmgr, kDifToggleDisabled,
                                                kDifToggleDisabled));
  IBEX_SPIN_FOR(lowpower_hint_is_cleared(), 100);
  irq_global_ctrl(true);
  clear_wakeup();

  LOG_INFO("Normal WFI");
  // Now do WFI without the LOW_POWER_HINT.
  irq_global_ctrl(false);
  set_timer(100);
  wait_for_interrupt();
  irq_global_ctrl(true);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  test_init();
  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) != true) {
    return false;
  }
  test_sleep(false);
  test_sleep(true);
  return true;
}
