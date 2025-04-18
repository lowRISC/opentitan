// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_rv_timer_t kRvTimerDt = 0;
static_assert(kDtRvTimerCount >= 1, "this test expects at least one rv_timer");
static const dt_alert_handler_t kAlertHandlerDt = 0;
static_assert(kDtAlertHandlerCount == 1, "this test expects an alert_handler");
static const dt_rv_core_ibex_t kRvCoreIbexDt = 0;
static_assert(kDtRvCoreIbexCount == 1, "this test expects exactly one Ibex");

typedef struct counters {
  uint32_t alert_raised;
  uint32_t wdog_barked;
  uint64_t elapsed_ticks;
} counters_t;

static volatile counters_t counters = {0};

static volatile dif_rv_core_ibex_nmi_state_t nmi_state;
static volatile bool ext_irq_fired = false;

static dif_pwrmgr_t pwrmgr;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_alert_handler_t alert_handler;
static dif_rv_timer_t timer;

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset)
 * but at the phase 1 (i.e. wipe secrets) the NMI interrupt handler should clear
 * the escalation.
 */
enum {
  kEscalationPhase0Micros = 100 * 1000,  // 100 ms
  kEscalationPhase2Micros = 100,         // 100 us
  kIrqDeadlineMicros = 10,               // 10 us
  kTick1us = 1 * 1000 * 1000,            // 1MHz - 1us.
  kHart = kTopEarlgreyPlicTargetIbex0,
  kTimeThresholdUs = 5000,  // 5ms expressed in microseconds.
};

static status_t set_tick(uint32_t tick_hz) {
  dif_rv_timer_tick_params_t tick_params;
  TRY(dif_rv_timer_approximate_tick_params(kClockFreqPeripheralHz, tick_hz,
                                           &tick_params));
  TRY(dif_rv_timer_set_tick_params(&timer, kHart, tick_params));
  return OK_STATUS();
}

static void alerts_configure_all(const dif_alert_handler_t *alert_handler,
                                 dif_alert_handler_config_t config,
                                 dif_toggle_t locked) {
  // Check lengths of alert, local alert, and class arrays.
  CHECK((config.alerts_len > 0 && config.alerts != NULL &&
         config.alert_classes != NULL) ||
        (config.alerts_len == 0 && config.alerts == NULL &&
         config.alert_classes == NULL));
  CHECK((config.local_alerts_len > 0 && config.local_alerts != NULL &&
         config.local_alert_classes != NULL) ||
        (config.local_alerts_len == 0 && config.local_alerts == NULL &&
         config.local_alert_classes == NULL));
  CHECK((config.classes_len > 0 && config.classes != NULL &&
         config.class_configs != NULL) ||
        (config.classes_len == 0 && config.classes == NULL &&
         config.class_configs == NULL));

  // Check that the provided ping timeout actually fits in the timeout
  // register, which is smaller than a native word length.
  CHECK(config.ping_timeout <=
        ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK);

  // Configure and enable the requested alerts.
  for (int i = 0; i < config.alerts_len; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        alert_handler, config.alerts[i], config.alert_classes[i],
        kDifToggleEnabled, locked));
  }

  // Configure and enable the requested local alerts.
  for (int i = 0; i < config.local_alerts_len; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_local_alert(
        alert_handler, config.local_alerts[i], config.local_alert_classes[i],
        kDifToggleEnabled, locked));
  }

  // Configure and enable the requested classes.
  for (int i = 0; i < config.classes_len; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        alert_handler, config.classes[i], config.class_configs[i],
        kDifToggleEnabled, locked));
  }
}

static void alert_handler_config(void) {
  uint32_t cycles[3] = {0};
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase0Micros, &cycles[0]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase2Micros, &cycles[1]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(kIrqDeadlineMicros,
                                                             &cycles[2]));
  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = cycles[0]},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = cycles[1]}};
  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = cycles[2],
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
      .ping_timeout = kAlertHandlerTestutilsDefaultPingTimeout,
  };

  alerts_configure_all(&alert_handler, config, /*lock=*/kDifToggleEnabled);

  CHECK_STATUS_OK(set_tick(kTick1us));
  counters.elapsed_ticks = 0;
  CHECK_DIF_OK(
      dif_rv_timer_counter_write(&timer, kHart, counters.elapsed_ticks));
  CHECK_DIF_OK(dif_rv_timer_counter_read(&timer, kHart,
                                         (uint64_t *)&counters.elapsed_ticks));
  CHECK(counters.elapsed_ticks == 0, "Failed to write the counter");

  CHECK_DIF_OK(
      dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, config.ping_timeout, kDifToggleEnabled,
      kDifToggleEnabled));
}

/**
 * Execute the alert handler NMI interrupt test.
 */
static void alert_handler_ping_ok_test(void) {
  alert_handler_config();

  uint64_t theshold_us = kTimeThresholdUs;
  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    theshold_us = theshold_us * 10;
    CHECK(theshold_us > kTimeThresholdUs, "Threshold overflow");
  }

  do {
    CHECK_DIF_OK(dif_rv_timer_counter_read(
        &timer, kHart, (uint64_t *)&counters.elapsed_ticks));
  } while (counters.elapsed_ticks < theshold_us);

  CHECK_DIF_OK(
      dif_rv_timer_counter_set_enabled(&timer, kHart, kDifToggleDisabled));
}

/**
 * OTTF external NMI internal IRQ handler.
 * This functions overrides the OTTF weak definition.
 */
void ottf_external_nmi_handler(uint32_t *exc_info) {
  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));

  if (nmi_state.wdog_barked) {
    counters.wdog_barked++;
  }
  if (nmi_state.alert_raised) {
    counters.alert_raised++;
  }

  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                kDifRvCoreIbexNmiSourceAll));
}

/**
 * OTTF external IRQ handler
 * This functions overrides the OTTF weak definition.
 */
void ottf_external_isr(uint32_t *exc_info) { ext_irq_fired = true; }

void init_peripherals(void) {
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kRvCoreIbexDt, &rv_core_ibex));

  CHECK_DIF_OK(dif_alert_handler_init_from_dt(kAlertHandlerDt, &alert_handler));

  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  CHECK_DIF_OK(dif_rv_timer_init_from_dt(kRvTimerDt, &timer));
  CHECK_DIF_OK(dif_rv_timer_reset(&timer));
}

bool test_main(void) {
  // Disable external interrupts via the PLIC entirely.
  // The NMI should still get through to the processor regardless.
  irq_global_ctrl(false);
  irq_external_ctrl(false);
  init_peripherals();

  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAll));

  alert_handler_ping_ok_test();

  // Double check that no external interrupts have occurred.
  CHECK(ext_irq_fired == false, "Unexpected external interrupt triggered.");
  CHECK(counters.alert_raised == 0, "Unexpected alert raised.");
  CHECK(counters.wdog_barked == 0, "Unexpected watchdog bark.");
  // Double check that the system has not been reset due to escalation and that
  // the reset reason is still POR.
  return UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0));
}
