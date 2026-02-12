// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/alert_handler.h"
#include "hw/top/dt/aon_timer.h"
#include "hw/top/dt/pwrmgr.h"
#include "hw/top/dt/rstmgr.h"
#include "hw/top/dt/rv_plic.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset) but
 * the phase 1 (i.e. wipe secrets) should occur and last during the time the
 * wdog is programmed to bark.
 */
enum {
  kWdogBarkMicros = 3 * 100,          // 300 us
  kWdogBiteMicros = 4 * 100,          // 400 us
  kEscalationPhase0Micros = 1 * 100,  // 100 us
  // The cpu value is set slightly larger, since if they are the same it is
  // possible busy_spin_micros in execute_test can complete before the
  // interrupt.
  kEscalationPhase0MicrosCpu = kEscalationPhase0Micros + 20,  // 120 us
  kEscalationPhase1Micros = 5 * 100,                          // 500 us
  kEscalationPhase2Micros = 100,                              // 100 us
};

static_assert(
    kWdogBarkMicros < kWdogBiteMicros &&
        kWdogBarkMicros > kEscalationPhase0Micros &&
        kWdogBarkMicros < (kEscalationPhase0Micros + kEscalationPhase1Micros) &&
        kWdogBiteMicros < (kEscalationPhase0Micros + kEscalationPhase1Micros),
    "The wdog bark and bite shall happens during the escalation phase 1");

/**
 * Objects to access the peripherals used in this test via dif API.
 */
enum {
  /**
   * PLIC target for the Ibex core.
   */
  kDtRvPlicTargetIbex0 = 0,
};

static dif_aon_timer_t aon_timer;
static dif_rv_plic_t plic;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t inst_id,
                     dif_rv_plic_irq_id_t plic_irq_id) {
  // Check if this is the AON timer peripheral
  if (inst_id == dt_aon_timer_instance_id(kDtAonTimerAon)) {
    // We should not get aon timer interrupts since escalation suppresses them.
    dt_aon_timer_irq_t irq =
        dt_aon_timer_irq_from_plic_id(kDtAonTimerAon, plic_irq_id);
    LOG_ERROR("Unexpected aon timer interrupt %d", irq);
    return true;
  }

  // Check if this is the alert handler peripheral
  if (inst_id == dt_alert_handler_instance_id(kDtAlertHandler)) {
    // Convert PLIC IRQ ID to alert handler IRQ
    dt_alert_handler_irq_t irq =
        dt_alert_handler_irq_from_plic_id(kDtAlertHandler, plic_irq_id);

    // Check the class.
    dif_alert_handler_class_state_t state;
    CHECK_DIF_OK(dif_alert_handler_get_class_state(
        &alert_handler, kDifAlertHandlerClassA, &state));
    CHECK(state == kDifAlertHandlerClassStatePhase0, "Wrong phase %d", state);

    // Deals with the alert cause: we expect it to be from the pwrmgr.
    dif_alert_handler_alert_t alert =
        dt_pwrmgr_alert_to_alert_id(kDtPwrmgrAon, kDtPwrmgrAlertFatalFault);
    bool is_cause = false;
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, alert, &is_cause));
    CHECK(is_cause);

    // Acknowledge the cause and irq; neither of them affect escalation.
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler, alert));
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, alert, &is_cause));
    CHECK(!is_cause);

    CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));
    return true;
  }

  return false;
}

/**
 * Initialize the peripherals used in this test.
 */
void init_peripherals(void) {
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kDtPwrmgrAon, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kDtRstmgrAon, &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kDtAonTimerAon, &aon_timer));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &plic));
  CHECK_DIF_OK(dif_alert_handler_init_from_dt(kDtAlertHandler, &alert_handler));

  // Enable AON timer interrupts in PLIC
  dt_plic_irq_id_t wkup_irq = dt_aon_timer_irq_to_plic_id(
      kDtAonTimerAon, kDtAonTimerIrqWkupTimerExpired);
  dt_plic_irq_id_t bark_irq =
      dt_aon_timer_irq_to_plic_id(kDtAonTimerAon, kDtAonTimerIrqWdogTimerBark);

  dt_plic_irq_id_t aon_irq_ids[] = {wkup_irq, bark_irq};
  for (size_t i = 0; i < ARRAYSIZE(aon_irq_ids); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, aon_irq_ids[i],
                                              /*priority=*/1u));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        &plic, aon_irq_ids[i], kDtRvPlicTargetIbex0, kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic, kDtRvPlicTargetIbex0,
                                                /*threshold=*/0u));
}

static uint32_t udiv64_slow_into_u32(uint64_t a, uint64_t b,
                                     uint64_t *rem_out) {
  const uint64_t result = udiv64_slow(a, b, rem_out);
  CHECK(result <= UINT32_MAX, "Result of division must fit in uint32_t");
  return (uint32_t)result;
}

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset) but
 * the phase 1 (i.e. wipe secrets) should occur and last during the time the
 * wdog is programed to bark.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[] = {
      dt_pwrmgr_alert_to_alert_id(kDtPwrmgrAon, kDtPwrmgrAlertFatalFault)};
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassA};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = udiv64_slow_into_u32(
           kEscalationPhase0Micros * kClockFreqPeripheralHz, 1000000, NULL)},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles = udiv64_slow_into_u32(
           kEscalationPhase1Micros * kClockFreqPeripheralHz, 1000000, NULL)},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = udiv64_slow_into_u32(
           kEscalationPhase2Micros * kClockFreqPeripheralHz, 1000000, NULL)}};

  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles =
          udiv64_slow_into_u32(10 * kClockFreqPeripheralHz, 1000000, NULL),
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
  }};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_config,
      .classes_len = ARRAYSIZE(class_config),
      .ping_timeout = kAlertHandlerTestutilsDefaultPingTimeout,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
}

/**
 * Execute the aon timer interrupt test.
 */
static void execute_test(dif_aon_timer_t *aon_timer) {
  uint32_t bark_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(kWdogBarkMicros,
                                                                &bark_cycles));
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(kWdogBiteMicros,
                                                                &bite_cycles));

  LOG_INFO(
      "Wdog will bark after %u/%u us/cycles and bite after %u/%u us/cycles",
      (uint32_t)kWdogBarkMicros, bark_cycles, (uint32_t)kWdogBiteMicros,
      bite_cycles);

  // Setup the wdog bark and bite timeouts.
  CHECK_STATUS_OK(
      aon_timer_testutils_watchdog_config(aon_timer, bark_cycles, bite_cycles,
                                          /*pause_in_sleep=*/false));

  // Trigger the alert handler to escalate.
  dif_pwrmgr_alert_t alert = kDifPwrmgrAlertFatalFault;
  CHECK_DIF_OK(dif_pwrmgr_alert_force(&pwrmgr, alert));
  busy_spin_micros(kEscalationPhase0MicrosCpu);

  // This should never run since escalation turns the CPU off.
  CHECK(false, "The alert handler failed to escalate");
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_peripherals();

  // Enable all the alert handler interrupts used in this test.
  dt_plic_irq_id_t classa_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassa);
  dt_plic_irq_id_t classb_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassb);
  dt_plic_irq_id_t classc_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassc);
  dt_plic_irq_id_t classd_irq = dt_alert_handler_irq_to_plic_id(
      kDtAlertHandler, kDtAlertHandlerIrqClassd);

  dt_plic_irq_id_t alert_irq_ids[] = {classa_irq, classb_irq, classc_irq,
                                      classd_irq};
  for (size_t i = 0; i < ARRAYSIZE(alert_irq_ids); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, alert_irq_ids[i],
                                              /*priority=*/1u));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        &plic, alert_irq_ids[i], kDtRvPlicTargetIbex0, kDifToggleEnabled));
  }

  alert_handler_config();

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoEscalation,
        "Wrong reset reason %02X", rst_info);

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, starting test");
    execute_test(&aon_timer);
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    LOG_INFO("Booting for the second time due to escalation reset");

    return true;
  } else {
    LOG_ERROR("Unexpected rst_info=0x%x", rst_info);
  }
  return false;
}
