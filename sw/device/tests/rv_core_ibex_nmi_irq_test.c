// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

typedef void (*isr_handler)(void);

static volatile isr_handler expected_isr_handler;
static volatile dif_rv_core_ibex_nmi_state_t nmi_state;
static volatile bool nmi_fired = false;

static dif_pwrmgr_t pwrmgr;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_aon_timer_t aon_timer;
static aon_timer_isr_ctx_t aon_timer_ctx = {
    .aon_timer = &aon_timer,
    .plic_aon_timer_start_irq_id =
        kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
};

static dif_rv_plic_t plic;
static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic,
    .hart_id = kTopEarlgreyPlicTargetIbex0,
};

static volatile dif_aon_timer_irq_t irq;
static dif_alert_handler_t alert_handler;
static alert_handler_isr_ctx_t alert_handler_ctx = {
    .alert_handler = &alert_handler,
    .plic_alert_handler_start_irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassa,
    .expected_irq = kDifAlertHandlerIrqClassb,
    .is_only_irq = false,
};

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset)
 * but at the phase 1 (i.e. wipe secrets)the nmi interrupt handler should clear
 * the escalation.
 */
enum {
  kEscalationPhase0Micros = 100 * 1000,  // 10 ms
  kEscalationPhase2Micros = 100,         // 100 us
  kIrqDeadlineMicros = 10,               // 10 us
  kWdogBarkMicros = 500,                 // 500 us
};

static void alert_handler_config(void) {
  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase0Micros)},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = alert_handler_testutils_get_cycles_from_us(
           kEscalationPhase2Micros)}};

  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles =
          alert_handler_testutils_get_cycles_from_us(kIrqDeadlineMicros),
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
  }};

  dif_alert_handler_alert_t alerts[] = {kTopEarlgreyAlertIdPwrmgrAonFatalFault};
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassA};
  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_config,
      .classes_len = ARRAYSIZE(class_config),
      .ping_timeout = 0,
  };

  alert_handler_testutils_configure_all(&alert_handler, config,
                                        /*lock=*/kDifToggleDisabled);
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
}

/**
 * Handle the wdog bark nmi irq.
 */
static void wdog_handler(void) {
  top_earlgrey_plic_peripheral_t peripheral;
  dif_aon_timer_irq_t irq;
  isr_testutils_aon_timer_isr(plic_ctx, aon_timer_ctx, &peripheral, &irq);
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));
}

/**
 * Handle the alert handler nmi irq.
 */
static void alert_handler_handler(void) {
  top_earlgrey_plic_peripheral_t peripheral;
  dif_alert_handler_irq_t irq;
  isr_testutils_alert_handler_isr(plic_ctx, alert_handler_ctx, &peripheral,
                                  &irq);

  // Check that the alert handler escalation can be stoped.
  bool can_clear;
  CHECK_DIF_OK(dif_alert_handler_escalation_can_clear(
      alert_handler_ctx.alert_handler, kDifAlertHandlerClassA, &can_clear));
  CHECK(can_clear, "Alert handler is locked.");

  CHECK_DIF_OK(dif_alert_handler_escalation_clear(
      alert_handler_ctx.alert_handler, kDifAlertHandlerClassA));
}

/**
 * Execute the wdog bark nmi interrupt test.
 */
static void wdog_nmi_test(void) {
  rv_plic_testutils_irq_range_enable(
      &plic, plic_ctx.hart_id, kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));

  // Setup to handle the incoming wdog nmi irq.
  expected_isr_handler = wdog_handler;
  nmi_fired = false;
  nmi_state = (dif_rv_core_ibex_nmi_state_t){0};

  // Setup the wdog bark interrupt.
  uint32_t count_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(kWdogBarkMicros);
  aon_timer_testutils_watchdog_config(&aon_timer,
                                      /*bark_cycles=*/count_cycles,
                                      /*bite_cycles=*/UINT32_MAX,
                                      /*pause_in_sleep=*/false);
  IBEX_SPIN_FOR(nmi_fired, kWdogBarkMicros * 2);

  // Check that the wdog nmi was enabled and barked during the nmi irq.
  CHECK(nmi_state.wdog_enabled && nmi_state.wdog_barked,
        "Wdog nmi state not expected:\n\t"
        "wdog_enable:%x\n\twdog_raised:%"
        "x\n",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);

  // Check that the wdog nmi is enable and is cleared.
  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));
  CHECK(nmi_state.wdog_enabled && !nmi_state.wdog_barked,
        "Wdog nmi state not expected:\n\t"
        "wdog_enable:%x\n\twdog_raised:%"
        "x\n",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);
}

/**
 * Execute the alert handler nmi interrupt test.
 */
static void alert_handler_nmi_test(void) {
  alert_handler_config();
  rv_plic_testutils_irq_range_enable(&plic, plic_ctx.hart_id,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa);
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAlert));

  // Setup to handle the incoming alert handler nmi irq.
  expected_isr_handler = alert_handler_handler;
  nmi_fired = false;

  // Trigger the alert handler to escalate.
  CHECK_DIF_OK(dif_pwrmgr_alert_force(&pwrmgr, kDifPwrmgrAlertFatalFault));

  IBEX_SPIN_FOR(nmi_fired, kEscalationPhase0Micros);

  // Check that the alert handler nmi was enabled and raised an alert during the
  // nmi irq.
  CHECK(nmi_state.alert_enabled && nmi_state.alert_raised,
        "Alert handler nmi state not expected:\n\t"
        "alert_enable:%x\n\talert_raised:%x\n",
        nmi_state.alert_enabled, nmi_state.alert_raised);

  // Check that the alert handler nmi is enabled and is cleared.
  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));
  CHECK(nmi_state.alert_enabled && !nmi_state.alert_raised,
        "Alert handler nmi state not expected:\n\t"
        "alert_enable:%x\n\talert_raised:%x\n",
        nmi_state.alert_enabled, nmi_state.alert_raised);
}

/**
 * OTTF external NMI internal IRQ handler.
 * This functions overrides the OTTF weak definition.
 * It calls the `expected_isr_handler` function pointer that is previously set
 * by the test to handler the specific peripheral irq.
 */
void ottf_external_nmi_handler(void) {
  nmi_fired = true;

  expected_isr_handler();

  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));
  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                kDifRvCoreIbexNmiSourceAll));
}

/**
 * Initialized all peripherals used in this test.
 */
void init_peripherals(void) {
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(addr, &plic));

  addr = mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(addr, &rv_core_ibex));

  addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(addr, &aon_timer));

  addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(addr, &alert_handler));

  addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(addr, &pwrmgr));
}
/**
 * This test do the following steps:
 * - Trigger a watchdog bark to generate a NMI.
 * - Check rv_core_ibex's NMI interrupt register and clear the interrupt.
 * - Repeat the previous steps with alert handler.
 */
bool test_main(void) {
  init_peripherals();
  alert_handler_nmi_test();
  wdog_nmi_test();

  return true;
}
