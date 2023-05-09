// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"
#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwm_regs.h"

typedef void (*isr_handler)(void);
static volatile isr_handler expected_isr_handler;
static volatile dif_rv_core_ibex_nmi_state_t nmi_state;
static volatile bool nmi_fired = false;
static volatile bool ext_irq_fired = false;
static volatile bool irq_is_pending = false;

static dif_aon_timer_t aon_timer;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_pwrmgr_t pwrmgr;
static dif_rv_timer_t rv_timer;
static dif_alert_handler_t alert_handler;
static dif_pwm_t pwm;
static dif_pinmux_t pinmux;
static dif_otp_ctrl_t otp_ctrl;
static dif_gpio_t gpio;

OTTF_DEFINE_TEST_CONFIG();

// ISRs

void ottf_external_isr(void) {
  LOG_INFO("got external IRQ");
  ext_irq_fired = true;
}

void ottf_external_nmi_handler(void) {
  nmi_fired = true;

  expected_isr_handler();

  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));
  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                kDifRvCoreIbexNmiSourceAll));
}

static void wdog_irq_handler(void) {
  bool is_pending;

  // The watchdog bark external interrupt is also connected to the NMI input of
  // rv_core_ibex.
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      &aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  irq_is_pending = is_pending;

  // Stop the watchdog.
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));

  // In order to handle the NMI we need to acknowledge the interrupt status bit
  // at the peripheral side.
  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(&aon_timer, kDifAonTimerIrqWdogTimerBark));
}

bool test_main(void) {
  // Define access to DUT IPs:
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR), &rv_timer));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_pwm_init(
      mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR), &pwm));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  LOG_INFO("Running CHIP Power Idle Load test");

  static const uint32_t kGpioMask = 0x00000004;

  CHECK_DIF_OK(
      dif_pinmux_output_select(&pinmux, (kTopEarlgreyPinmuxMioOutIoa0 + 2),
                               (kTopEarlgreyPinmuxOutselGpioGpio0 + 2)));

  // Set output modes of all GPIO pins
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, kGpioMask));

  // Write to set IOA2 low at the start of the test:
  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 0));

  LOG_INFO("GPIO active");

  // RV Timer
  static const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;
  static const uint32_t kComparator = 0;
  static const uint64_t kTickFreqHz = 1000000;
  static const uint64_t kDeadline = UINT32_MAX;

  CHECK_DIF_OK(dif_rv_timer_reset(&rv_timer));

  dif_rv_timer_tick_params_t rv_timer_tick_params;
  CHECK_DIF_OK(dif_rv_timer_approximate_tick_params(
      kClockFreqPeripheralHz, kTickFreqHz, &rv_timer_tick_params));
  // Configure the tick params for a particular hart's counter
  CHECK_DIF_OK(
      dif_rv_timer_set_tick_params(&rv_timer, kHart, rv_timer_tick_params));

  uint64_t current_time;
  CHECK_DIF_OK(dif_rv_timer_counter_read(&rv_timer, kHart, &current_time));
  CHECK_DIF_OK(dif_rv_timer_arm(&rv_timer, kHart, kComparator,
                                (current_time + kDeadline)));
  CHECK_DIF_OK(
      dif_rv_timer_counter_set_enabled(&rv_timer, kHart, kDifToggleEnabled));

  LOG_INFO("RV Timer active");

  // Alert Ping

  // 1. Config structs for all Incoming Alerts:
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // 2. Config structs for Local Alerts
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail};
  dif_alert_handler_class_t loc_alert_classes[] = {kDifAlertHandlerClassB};

  // 3. Config structs for Escalation phase
  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};
  // Escalation protocol (struct) for an alert class
  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = UINT16_MAX,
      .irq_deadline_cycles = UINT32_MAX,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };
  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};
  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};

  // 4. Runtime configuration (struct) for the alert handler:
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .local_alerts = loc_alerts,
      .local_alert_classes = loc_alert_classes,
      .local_alerts_len = ARRAYSIZE(loc_alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = UINT16_MAX,
  };

  // 5. Configure Alerts
  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));

  // Checks whether alert handler's ping timer is locked
  bool is_locked;
  CHECK_DIF_OK(
      dif_alert_handler_is_ping_timer_locked(&alert_handler, &is_locked));
  CHECK(is_locked, "Expected alerts to be locked");

  LOG_INFO("Alert ping is active");

  // PWM
  static const dif_pwm_config_t config_ = {
      .clock_divisor = 0,
      .beats_per_pulse_cycle = 32,
  };

  // Configuration struct for a specific PWM channel
  static const dif_pwm_channel_config_t default_ch_cfg_ = {
      .duty_cycle_a = 0,
      .duty_cycle_b = 0,
      .phase_delay = 0,
      .mode = kDifPwmModeFirmware,
      .polarity = kDifPwmPolarityActiveHigh,
      .blink_parameter_x = 0,
      .blink_parameter_y = 0,
  };
  static const dif_pwm_channel_t kPwmChannel[PWM_PARAM_N_OUTPUTS] = {
      kDifPwmChannel0, kDifPwmChannel1, kDifPwmChannel2,
      kDifPwmChannel3, kDifPwmChannel4, kDifPwmChannel5,
  };
  // Duty cycle (arbitrary) values (in the beats)
  static volatile const uint16_t kPwmDutycycle[PWM_PARAM_N_OUTPUTS] = {
      6, 11, 27, 8, 17, 7,
  };

  static const dif_pinmux_index_t kPinmuxMioOut[PWM_PARAM_N_OUTPUTS] = {
      kTopEarlgreyPinmuxMioOutIob10, kTopEarlgreyPinmuxMioOutIob11,
      kTopEarlgreyPinmuxMioOutIob12, kTopEarlgreyPinmuxMioOutIoc10,
      kTopEarlgreyPinmuxMioOutIoc11, kTopEarlgreyPinmuxMioOutIoc12,
  };
  static const dif_pinmux_index_t kPinmuxOutsel[PWM_PARAM_N_OUTPUTS] = {
      kTopEarlgreyPinmuxOutselPwmAonPwm0, kTopEarlgreyPinmuxOutselPwmAonPwm1,
      kTopEarlgreyPinmuxOutselPwmAonPwm2, kTopEarlgreyPinmuxOutselPwmAonPwm3,
      kTopEarlgreyPinmuxOutselPwmAonPwm4, kTopEarlgreyPinmuxOutselPwmAonPwm5,
  };

  CHECK_DIF_OK(dif_pwm_configure(&pwm, config_));

  // Confugure each of the PWM channels:
  dif_pwm_channel_config_t channel_config_ = default_ch_cfg_;
  for (int i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
    CHECK_DIF_OK(
        dif_pwm_channel_set_enabled(&pwm, kPwmChannel[i], kDifToggleDisabled));
    channel_config_.duty_cycle_a = kPwmDutycycle[i];
    CHECK_DIF_OK(
        dif_pwm_configure_channel(&pwm, kPwmChannel[i], channel_config_));
    CHECK_DIF_OK(
        dif_pwm_channel_set_enabled(&pwm, kPwmChannel[i], kDifToggleEnabled));
  }

  // Enable all PWM channels
  CHECK_DIF_OK(dif_pwm_phase_cntr_set_enabled(&pwm, kDifToggleEnabled));

  // PINMUX
  for (int i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_output_select(&pinmux, kPinmuxMioOut[i], kPinmuxOutsel[i]));
  }

  LOG_INFO("PWM active");

  // OTP

  static const dif_otp_ctrl_config_t otp_ctrl_config = {
      .check_timeout = UINT32_MAX,
      .integrity_period_mask = 0x1,
      .consistency_period_mask = 0x1,
  };

  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp_ctrl, otp_ctrl_config));

  LOG_INFO("OTP periodic checks active");

  // AON Timer - activate in Watchdog mode (not wakeup mode) & IRQ
  static const uint64_t kTimeTillBark = 1000;

  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));
  CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&aon_timer));
  expected_isr_handler = wdog_irq_handler;
  nmi_fired = false;
  nmi_state = (dif_rv_core_ibex_nmi_state_t){0};
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));
  uint32_t count_cycles = 0;
  CHECK_STATUS_OK(
      aon_timer_testutils_get_aon_cycles_from_us(kTimeTillBark, &count_cycles));
  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(&aon_timer, count_cycles,
                                                      UINT32_MAX, false));

  LOG_INFO("AON Timer active");

  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 1));
  LOG_INFO("all HW is active");
  IBEX_SPIN_FOR(nmi_fired, kTimeTillBark * 2);

  // Note, if running on DV environment: We wait here for the AON Timer to issue
  // an NMI. This will make the SW exit with "true" and the Verilog test to
  // finish with "pass". Without this, the CPU will remain idle and the
  // simulator will end the test (due to simulation timeout) with "fail".

  CHECK_DIF_OK(dif_pwm_phase_cntr_set_enabled(&pwm, kDifToggleDisabled));
  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 0));

  // Prepare to exit
  LOG_INFO("Prepare to exit");

  // We expect the watchdog bark interrupt to be pending on the peripheral side.
  CHECK(irq_is_pending, "Expected watchdog bark interrupt to be pending");

  // Check NMI previous state (before clearing):
  CHECK(nmi_state.wdog_enabled && nmi_state.wdog_barked,
        "WDOG NMI state check1 not expected! wdog_enable:%x, wdog_raised:%x",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);

  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));
  // Check NMI current state (after clearing):
  CHECK(nmi_state.wdog_enabled && !nmi_state.wdog_barked,
        "WDOG NMI state check2 not expected! wdog_enable:%x wdog_raised:%x",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);

  // Check that no external interrupts have occurred.
  CHECK(ext_irq_fired == false, "Unexpected external interrupt triggered.");

  // Check that the system has not been reset due to escalation and that the
  // reset reason is still POR.
  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true);

  CHECK_STATUS_OK(aon_timer_testutils_shutdown(&aon_timer));

  test_status_set(kTestStatusInTest);

  return true;
}
