// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Included code:

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
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

// Global Variables

typedef void (*isr_handler)(void);
static volatile isr_handler expected_isr_handler;
static volatile dif_rv_core_ibex_nmi_state_t nmi_state;
static volatile bool nmi_fired = false;
static volatile bool ext_irq_fired = false;
static volatile bool irq_is_pending = false;

static dif_aon_timer_t aon_timer;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t rv_plic;
static dif_pwrmgr_t pwrmgr;
static dif_rv_timer_t rv_timer;
static dif_alert_handler_t alert_handler;
static dif_pwm_t pwm;
static dif_pinmux_t pinmux;
static dif_otp_ctrl_t otp_ctrl;
static dif_gpio_t gpio;
static dif_adc_ctrl_t adc_ctrl;

static volatile const bool kCoreClkOff = false;
static volatile const bool kIoClkOff = false;
static volatile const bool kUsbSlpOff = false;
static volatile const bool kUsbActOff = false;
static volatile const bool kDeepSleep = false;

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

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

// Specific handlee for the wdog bark NMI IRQ.
static void wdog_irq_handler(void) {
  bool is_pending;

  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      &aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  irq_is_pending = is_pending;

  // Stop the watchdog.
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));

  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(&aon_timer, kDifAonTimerIrqWdogTimerBark));

  // Signal a software interrupt
  dif_rv_plic_t rv_plic_isr;
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &rv_plic_isr));
  CHECK_DIF_OK(dif_rv_plic_software_irq_force(&rv_plic_isr, kPlicTarget));
}

// Functions

void prepare_to_exit(void) {
  CHECK_DIF_OK(dif_pwm_phase_cntr_set_enabled(&pwm, kDifToggleDisabled));

  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 0));

  LOG_INFO("Prepare to exit");

  // Check that no external interrupts have occurred.
  CHECK(ext_irq_fired == false, "Unexpected external interrupt triggered.");

  CHECK_STATUS_OK(aon_timer_testutils_shutdown(&aon_timer));

  // Set the test status flag back to "TestStatusInTest"
  test_status_set(kTestStatusInTest);
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
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));

  LOG_INFO("Running CHIP Power Sleep Load test");

  // Testplan: "The test should set a GPIO (mapped to the IOA2 pin) to high
  // while the power state of interest is active"

  const uint32_t kGpioMask = 0x00000004;

  // PINMUX
  CHECK_DIF_OK(
      dif_pinmux_output_select(&pinmux, (kTopEarlgreyPinmuxMioOutIoa0 + 2),
                               (kTopEarlgreyPinmuxOutselGpioGpio0 + 2)));

  // Set output modes of all GPIO pins
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, kGpioMask));

  // Write to set IOA2 low at the start of the test:
  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 0));

  LOG_INFO("GPIO active");

  // PWRMGR- Read wakeup reason

  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
  LOG_INFO("wakeup type:%d. wakeup reason: 0x%02X", wakeup_reason.types,
           wakeup_reason.request_sources);

  if (wakeup_reason.types == 0) {
    // Wakeup due to Power Up - DO NOTHING HERE - go on with the rest of the
    // test's flow....
  } else if ((wakeup_reason.types == kDifPwrmgrWakeupTypeRequest) &&
             (wakeup_reason.request_sources ==
              kDifPwrmgrWakeupRequestSourceFive)) {
    // Wakeup due to a peripheral request and reason is AON Timer
    prepare_to_exit();
    return true;
  } else {
    LOG_ERROR("unexpected wakeup reason! type=0x%x, source=0x%x",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  // RV Timer
  const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;
  const uint32_t kComparator = 0;
  const uint64_t kTickFreqHz = 1000000;
  const uint64_t kDeadline = UINT32_MAX;

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
  for (size_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
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

  // Configuration struct for PWM general
  const dif_pwm_config_t config_ = {
      .clock_divisor = 0,
      .beats_per_pulse_cycle = 32,
  };

  // Configuration struct for a specific PWM channel
  const dif_pwm_channel_config_t default_ch_cfg_ = {
      .duty_cycle_a = 0,
      .duty_cycle_b = 0,
      .phase_delay = 0,
      .mode = kDifPwmModeFirmware,
      .polarity = kDifPwmPolarityActiveHigh,
      .blink_parameter_x = 0,
      .blink_parameter_y = 0,
  };
  const dif_pwm_channel_t kPwmChannel[PWM_PARAM_N_OUTPUTS] = {
      kDifPwmChannel0, kDifPwmChannel1, kDifPwmChannel2,
      kDifPwmChannel3, kDifPwmChannel4, kDifPwmChannel5,
  };
  // Duty cycle (arbitrary) values (in the beats)
  const uint16_t kPwmDutycycle[PWM_PARAM_N_OUTPUTS] = {
      6, 11, 27, 8, 17, 7,
  };

  const dif_pinmux_index_t kPinmuxMioOut[PWM_PARAM_N_OUTPUTS] = {
      kTopEarlgreyPinmuxMioOutIob10, kTopEarlgreyPinmuxMioOutIob11,
      kTopEarlgreyPinmuxMioOutIob12, kTopEarlgreyPinmuxMioOutIoc10,
      kTopEarlgreyPinmuxMioOutIoc11, kTopEarlgreyPinmuxMioOutIoc12,
  };
  const dif_pinmux_index_t kPinmuxOutsel[PWM_PARAM_N_OUTPUTS] = {
      kTopEarlgreyPinmuxOutselPwmAonPwm0, kTopEarlgreyPinmuxOutselPwmAonPwm1,
      kTopEarlgreyPinmuxOutselPwmAonPwm2, kTopEarlgreyPinmuxOutselPwmAonPwm3,
      kTopEarlgreyPinmuxOutselPwmAonPwm4, kTopEarlgreyPinmuxOutselPwmAonPwm5,
  };

  CHECK_DIF_OK(dif_pwm_configure(&pwm, config_));

  // Configure each of the PWM channels:
  dif_pwm_channel_config_t channel_config_ = default_ch_cfg_;
  for (size_t i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
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
  for (size_t i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_output_select(&pinmux, kPinmuxMioOut[i], kPinmuxOutsel[i]));
  }

  LOG_INFO("PWM active");

  // OTP

  // Configure OTP Control to do periodic "consistency" & "integrity" checks.
  const dif_otp_ctrl_config_t otp_ctrl_config = {
      .check_timeout = UINT32_MAX,
      .integrity_period_mask = 0x1,
      .consistency_period_mask = 0x1,
  };

  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp_ctrl, otp_ctrl_config));

  LOG_INFO("OTP periodic checks active");

  // AON Timer
  const uint64_t kTimeTillBark = 1000;

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

  if (kDeepSleep) {
    // activate in Wakeup mode (no need for IRQ)
    CHECK_STATUS_OK(
        aon_timer_testutils_wakeup_config(&aon_timer, kTimeTillBark));
  } else {
    // Unmask the software interrupt so it can be used to bring the CPU out of
    // sleep without having an NMI race WFI.
    irq_software_ctrl(/*en=*/true);

    // activate in Watchdog mode & IRQ
    CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(
        &aon_timer, count_cycles, UINT32_MAX, false));
  }
  LOG_INFO("AON Timer active");

  // ADC Controller
  const uint8_t kNumLowPowerSamples = 2;
  const uint8_t kNumNormalPowerSamples = 1;
  const uint64_t kPowerUpTime = 30;
  const uint64_t kWakeUpTime = 500;
  uint32_t power_up_time_aon_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(
      kPowerUpTime, &power_up_time_aon_cycles));
  uint32_t wake_up_time_aon_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(
      kWakeUpTime, &wake_up_time_aon_cycles));

  // ADC configuration
  CHECK_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl, kDifToggleDisabled));
  CHECK_DIF_OK(dif_adc_ctrl_reset(&adc_ctrl));
  CHECK(power_up_time_aon_cycles < UINT8_MAX,
        "power_up_time_aon_cycles must fit into uint8_t");
  CHECK_DIF_OK(dif_adc_ctrl_configure(
      &adc_ctrl,
      (dif_adc_ctrl_config_t){
          .mode = kDifAdcCtrlLowPowerScanMode,
          .num_low_power_samples = kNumLowPowerSamples,
          .num_normal_power_samples = kNumNormalPowerSamples,
          .power_up_time_aon_cycles = (uint8_t)power_up_time_aon_cycles + 1,
          .wake_up_time_aon_cycles = wake_up_time_aon_cycles}));
  CHECK_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl, kDifToggleEnabled));

  LOG_INFO("ADC Controller active");

  // Power Manager
  dif_pwrmgr_domain_config_t pwrmgr_cfg;
  dif_pwrmgr_request_sources_t pwrmgr_wakeups;

  // Specify which request sources are enabled for wake-up
  pwrmgr_wakeups =
      (kDifPwrmgrWakeupRequestSourceOne | kDifPwrmgrWakeupRequestSourceTwo |
       kDifPwrmgrWakeupRequestSourceThree | kDifPwrmgrWakeupRequestSourceFour |
       kDifPwrmgrWakeupRequestSourceFive | kDifPwrmgrWakeupRequestSourceSix);

  // Power manager configuration
  pwrmgr_cfg = ((kCoreClkOff ? 0 : kDifPwrmgrDomainOptionCoreClockInLowPower) |
                (kIoClkOff ? 0 : kDifPwrmgrDomainOptionIoClockInLowPower) |
                (kUsbSlpOff ? 0 : kDifPwrmgrDomainOptionUsbClockInLowPower) |
                (kUsbActOff ? 0 : kDifPwrmgrDomainOptionUsbClockInActivePower) |
                (kDeepSleep ? 0 : kDifPwrmgrDomainOptionMainPowerInLowPower));
  CHECK_STATUS_OK(
      pwrmgr_testutils_enable_low_power(&pwrmgr, pwrmgr_wakeups, pwrmgr_cfg));
  LOG_INFO("Power Manage configured");

  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 1));
  LOG_INFO("all HW is active");
  test_status_set(0xff20);
  wait_for_interrupt();

  // Check for software interrupt and clear. Re-initialize the struct in case
  // the software interrupt did not happen.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &rv_plic));
  bool software_irq_pending;
  CHECK_DIF_OK(dif_rv_plic_software_irq_is_pending(&rv_plic, kPlicTarget,
                                                   &software_irq_pending));
  CHECK(software_irq_pending,
        "Software IRQ unexpectedly not pending after WFI");
  CHECK_DIF_OK(dif_rv_plic_software_irq_acknowledge(&rv_plic, kPlicTarget));

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

  prepare_to_exit();
  return true;
}
