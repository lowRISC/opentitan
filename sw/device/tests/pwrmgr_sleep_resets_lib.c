// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/pwrmgr_sleep_resets_lib.h"

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static_assert(
    kWdogBarkMicros < kWdogBiteMicros &&
        kWdogBarkMicros > kEscalationPhase0Micros &&
        kWdogBarkMicros < (kEscalationPhase0Micros + kEscalationPhase1Micros) &&
        kWdogBiteMicros < (kEscalationPhase0Micros + kEscalationPhase1Micros),
    "The wdog bark and bite shall happens during the escalation phase 1");

dif_flash_ctrl_state_t *flash_ctrl;
dif_rv_plic_t *plic;
dif_alert_handler_t *alert_handler;
dif_aon_timer_t *aon_timer;
dif_pwrmgr_t *pwrmgr;
dif_sysrst_ctrl_t *sysrst_ctrl_aon;
dif_rstmgr_t *rstmgr;

dif_flash_ctrl_state_t flash_ctrl_actual;
dif_rv_plic_t plic_actual;
dif_alert_handler_t alert_handler_actual;
dif_aon_timer_t aon_timer_actual;
dif_pwrmgr_t pwrmgr_actual;
dif_sysrst_ctrl_t sysrst_ctrl_aon_actual;
dif_rstmgr_t rstmgr_actual;

void init_peripherals(void) {
  // Initialize pwrmgr.
  CHECK_DIF_OK(
      dif_pwrmgr_init(mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR),
                      &pwrmgr_actual));
  pwrmgr = &pwrmgr_actual;

  // Initialize sysrst_ctrl.
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl_aon_actual));
  sysrst_ctrl_aon = &sysrst_ctrl_aon_actual;

  // Initialize rstmgr to check the reset reason.
  CHECK_DIF_OK(
      dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr_actual));
  rstmgr = &rstmgr_actual;

  // Initialize aon timer to use the wdog.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
      &aon_timer_actual));
  aon_timer = &aon_timer_actual;

  // Initialize flash_ctrl
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl_actual,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  flash_ctrl = &flash_ctrl_actual;

  // Initialize plic.
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic_actual));
  plic = &plic_actual;

  rv_plic_testutils_irq_range_enable(
      plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // Initialize alert handler.
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler_actual));
  alert_handler = &alert_handler_actual;
}

void config_alert_handler(void) {
  dif_alert_handler_alert_t alerts[] = {kTopEarlgreyAlertIdPwrmgrAonFatalFault};
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassA};

  uint32_t cycles[4] = {0};
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase0Micros, &cycles[0]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase1Micros, &cycles[1]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase2Micros, &cycles[2]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(10, &cycles[3]));

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles =
           cycles[0] * alert_handler_testutils_cycle_rescaling_factor()},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles =
           cycles[1] * alert_handler_testutils_cycle_rescaling_factor()},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles =
           cycles[2] * alert_handler_testutils_cycle_rescaling_factor()}};

  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles =
          cycles[3] * alert_handler_testutils_cycle_rescaling_factor(),
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
      .ping_timeout = 0,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(alert_handler, config,
                                                        kDifToggleEnabled));
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
}

void config_sysrst(dif_pinmux_index_t pad_pin) {
  LOG_INFO("sysrst enabled");

  // Set sysrst as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceOne,
                                              kDifToggleEnabled));
  LOG_INFO("Reset Request SourceOne is set");

  // Configure sysrst key combo
  // reset pulse : 50 us
  // detect duration : 50 us

  dif_sysrst_ctrl_key_combo_config_t sysrst_ctrl_key_combo_config = {
      .keys = kDifSysrstCtrlKeyAll,
      .detection_time_threshold = 10,
      .actions = kDifSysrstCtrlKeyComboActionAll,
      .embedded_controller_reset_duration = 10};

  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      sysrst_ctrl_aon, kDifSysrstCtrlKeyCombo0, sysrst_ctrl_key_combo_config));
  // Configure sysrst input change
  // debounce duration : 100 us
  dif_sysrst_ctrl_input_change_config_t sysrst_ctrl_input_change_config = {
      .input_changes = kDifSysrstCtrlInputAll, .debounce_time_threshold = 20};

  // Configure pinmux
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      sysrst_ctrl_aon, sysrst_ctrl_input_change_config));

  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In, pad_pin));
}

void config_wdog(uint64_t bark_micros, uint64_t bite_micros) {
  uint32_t bark_cycles = 0;
  CHECK_STATUS_OK(
      aon_timer_testutils_get_aon_cycles_from_us(bark_micros, &bark_cycles));
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(
      aon_timer_testutils_get_aon_cycles_from_us(bite_micros, &bite_cycles));

  LOG_INFO("Wdog will bark after %u microseconds (%u aon cycles)",
           (uint32_t)bark_micros, bark_cycles);
  LOG_INFO("Wdog will bite after %u microseconds (%u aon cycles)",
           (uint32_t)bite_micros, bite_cycles);

  // Setup the wdog bark and bite timeouts.
  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(aon_timer, bark_cycles,
                                                      bite_cycles, false));
  // Set wdog as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
}

void trigger_escalation(void) {
  // The relative times of escalation, time, and bark are set so the aon timer
  // won't trigger bark nor bite.
  config_wdog(
      kWdogBarkMicros * alert_handler_testutils_cycle_rescaling_factor(),
      kWdogBiteMicros * alert_handler_testutils_cycle_rescaling_factor());
  // Trigger the alert handler to escalate.
  dif_pwrmgr_alert_t alert = kDifPwrmgrAlertFatalFault;
  CHECK_DIF_OK(dif_pwrmgr_alert_force(pwrmgr, alert));

  // If this busy spin expires the escalation didn't occur as expected.
  busy_spin_micros(kWdogBiteMicros);
  CHECK(false, "Timeout waiting for escalation to occur.");
}

void enter_sleep_no_resets_enabled(bool deep_sleep) {
  dif_pwrmgr_domain_config_t config =
      deep_sleep ? 0
                 : kDifPwrmgrDomainOptionUsbClockInLowPower |
                       kDifPwrmgrDomainOptionCoreClockInLowPower |
                       kDifPwrmgrDomainOptionIoClockInLowPower |
                       kDifPwrmgrDomainOptionMainPowerInLowPower;

  // Program the pwrmgr to go to deep sleep state (clocks off).
  // Enter in low power mode.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(pwrmgr, 0, config));
  wait_for_interrupt();

  // If we arrive here the test must fail.
  CHECK(false, "Fail to reset from low power entry!");
}

void enter_sleep_for_wdog(bool deep_sleep) {
  dif_pwrmgr_domain_config_t config =
      deep_sleep ? 0
                 : kDifPwrmgrDomainOptionUsbClockInLowPower |
                       kDifPwrmgrDomainOptionCoreClockInLowPower |
                       kDifPwrmgrDomainOptionIoClockInLowPower |
                       kDifPwrmgrDomainOptionMainPowerInLowPower;

  // Program the pwrmgr to go to deep sleep state (clocks off).
  // Enter in low power mode.
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      pwrmgr, kDifPwrmgrWakeupRequestSourceTwo, config));
  wait_for_interrupt();

  // If we arrive here the test must fail.
  CHECK(false, "Fail to reset from low power entry!");
}

void enter_sleep_for_sysrst(bool deep_sleep) {
  // Place device into low power and immediately wake.
  dif_pwrmgr_domain_config_t config =
      deep_sleep ? 0
                 : kDifPwrmgrDomainOptionUsbClockInLowPower |
                       kDifPwrmgrDomainOptionCoreClockInLowPower |
                       kDifPwrmgrDomainOptionIoClockInLowPower |
                       kDifPwrmgrDomainOptionMainPowerInLowPower;
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      pwrmgr, kDifPwrmgrWakeupRequestSourceOne, config));
  // Log message to synchronize with host side: emit it as close as
  // possible before WFI so the host has no chance of sending the reset
  // before it is enabled.
  LOG_INFO("Sysrst reset in %s sleep mode", deep_sleep ? "deep" : "normal");
  // Enter in low power mode.
  wait_for_interrupt();

  // If we arrive here the test must fail.
  CHECK(false, "Fail to reset from low power entry!");
}

void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral;
  dif_rv_plic_irq_id_t irq_id;
  uint32_t irq = 0;
  uint32_t alert = 0;

  CHECK_DIF_OK(dif_rv_plic_irq_claim(plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq =
        (dif_aon_timer_irq_t)(irq_id -
                              (dif_rv_plic_irq_id_t)
                                  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    // Stops escalation process.
    CHECK_DIF_OK(dif_alert_handler_escalation_clear(alert_handler,
                                                    kDifAlertHandlerClassA));
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(aon_timer, irq));

    CHECK(irq != kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark,
          "AON Timer Wdog should not bark");

  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    irq = (dif_rv_plic_irq_id_t)(irq_id -
                                 (dif_rv_plic_irq_id_t)
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa);

    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(alert_handler, alert));

    dif_alert_handler_class_state_t state;
    CHECK_DIF_OK(dif_alert_handler_get_class_state(
        alert_handler, kDifAlertHandlerClassA, &state));

    CHECK(state == kDifAlertHandlerClassStatePhase0, "Wrong phase %d", state);

    CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(alert_handler, irq));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic, kPlicTarget, irq_id));
}
