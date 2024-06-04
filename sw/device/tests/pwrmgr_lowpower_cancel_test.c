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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"

dif_pwrmgr_t pwrmgr;
dif_rv_plic_t rv_plic;

static dif_pwrmgr_request_sources_t wakeup_src =
    kDifPwrmgrWakeupRequestSourceFive;
static uint32_t wakeup_source = PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX;

static dif_aon_timer_t timer;

void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(&rv_plic, kTopEarlgreyPlicTargetIbex0, &irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    LOG_INFO("AON Timer ISR");
    dif_aon_timer_irq_t irq =
        (dif_aon_timer_irq_t)(irq_id -
                              (dif_rv_plic_irq_id_t)
                                  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    if (irq_id == kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired) {
      CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&timer));
    } else if (irq_id == kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark) {
      CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&timer));
    }
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&timer, irq));
    bool is_pending = true;
    CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
        &timer, kDifAonTimerIrqWkupTimerExpired, &is_pending));
    CHECK(!is_pending);
  } else if (peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon) {
    LOG_INFO("Pwrmgr ISR");
    dif_pwrmgr_irq_t irq =
        (dif_pwrmgr_irq_t)(irq_id - (dif_rv_plic_irq_id_t)
                                        kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
    CHECK(irq == kDifPwrmgrIrqWakeup, "Pwrmgr IRQ ID: %d is incorrect", irq);
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, irq));
  } else {
    CHECK(false, "IRQ peripheral: %d is incorrect", peripheral);
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register
  CHECK_DIF_OK(
      dif_rv_plic_irq_complete(&rv_plic, kTopEarlgreyPlicTargetIbex0, irq_id));
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

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));

  // Enable AON interrupts.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
  rv_plic_testutils_irq_range_enable(
      &rv_plic, kTopEarlgreyPlicTargetIbex0,
      kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &timer));
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
  LOG_INFO("Woke up by source %d", wakeup_source);
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
