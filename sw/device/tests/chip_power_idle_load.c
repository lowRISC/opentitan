// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//==============================================================================
// Included code:

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"  // Memory-mapped IO functions
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/runtime/hart.h"  // functions for excution halt-like functionality
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "aon_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Top-specific Definitions
#include "pwm_regs.h"

//==============================================================================
// Global Variables

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

//==============================================================================
OTTF_DEFINE_TEST_CONFIG();

//==============================================================================
// Exception handlers
// ...using the default OTTF exception handlers...

//==============================================================================
// ISRs

// ------------------------------------
// OTTF External-IRQ handler
// (this functions overrides the OTTF weak definition)
void ottf_external_isr(void) {
  LOG_INFO("SW_INFO: got external IRQ");
  ext_irq_fired = true;
}

// ------------------------------------
// OTTF external NMI internal IRQ handler.
// This functions overrides the OTTF weak definition.
// It calls `expected_isr_handler` function pointer that is previously set by
// the test for the specific peripheral.
void ottf_external_nmi_handler(void) {
  nmi_fired = true;

  expected_isr_handler();  // this calls the specific handler as defined in
                           // "test_main"

  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t
                          *)&nmi_state));  // get the state before clearing
  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(
      &rv_core_ibex, kDifRvCoreIbexNmiSourceAll));  // clear
}

// ------------------------------------
// Specific handlee for the wdog bark NMI IRQ.
static void wdog_irq_handler(void) {
  bool is_pending;

  // The watchdog bark external interrupt is also connected to the NMI input of
  // rv_core_ibex. We therefore expect the interrupt to be pending on the
  // peripheral side (the check is done later in the test function).
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      &aon_timer, kDifAonTimerIrqWdogTimerBark,
      &is_pending));  // (this wants "bool" not "volatile bool")
  irq_is_pending = is_pending;

  // Stop the watchdog.
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));

  // In order to handle the NMI we need to acknowledge the interrupt status bit
  // at the peripheral side. Note that this test does not use the PLIC, so there
  // is nothing to acknowledge on the PLIC side. We are hence not using the
  // isr_testutils_aon_timer_isr function here.
  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(&aon_timer, kDifAonTimerIrqWdogTimerBark));
}

//==============================================================================
bool test_main(void) {
  // ------------------------------------
  // Define access to DUT IPs:
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
      &aon_timer));  // AON Timer
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));  // IBEX core
  CHECK_DIF_OK(
      dif_pwrmgr_init(mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR),
                      &pwrmgr));  // PWRMGR
  CHECK_DIF_OK(
      dif_rv_timer_init(mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR),
                        &rv_timer));  // RV Timer
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));  //
  CHECK_DIF_OK(dif_pwm_init(
      mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR), &pwm));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR),
      &otp_ctrl));  // OTP Controller
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  LOG_INFO("SW_INFO: Running CHIP Power Idle Load test");

  // ------------------------------------
  // Testplan: "The test should set a GPIO (mapped to the IOA2 pin) to high
  // while the power state of interest is active"

  static const uint32_t kGpioMask = 0x00000004;  // use pin 2
  //                                            // "If the Nth bit is enabled,
  //                                            then the Nth pin is selected by
  //                                            the mask"

  // PINMUX -   // Set a connection between a MIO pad output and peripheral
  // output
  CHECK_DIF_OK(dif_pinmux_output_select(
      &pinmux, (kTopEarlgreyPinmuxMioOutIoa0 + 2),
      (kTopEarlgreyPinmuxOutselGpioGpio0 + 2)));  // pinmux config

  // Set output modes of all GPIO pins
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, kGpioMask));

  // Write to set IOA2 low at the start of the test:
  CHECK_DIF_OK(dif_gpio_write(&gpio, 2, 0));

  // ------------------------------------
  // RV Timer
  static const uint32_t kHart = (uint32_t)kTopEarlgreyPlicTargetIbex0;
  static const uint32_t kComparator = 0;
  static const uint64_t kTickFreqHz =
      1000000;  // 1 MHz so each timer tick is 1[us]
  static const uint64_t kDeadline = UINT32_MAX;

  CHECK_DIF_OK(
      dif_rv_timer_reset(&rv_timer));  // reset the timer, disabling all IRQs,
                                       // counters, and comparators

  dif_rv_timer_tick_params_t
      rv_timer_tick_params;  // struct to hold the timekeeping parameters for
                             // the timer
  // Generate an aproximate `dif_rv_timer_tick_params_t` given the device clock
  // frequency and desired counter frequency (both given in Hertz).
  CHECK_DIF_OK(dif_rv_timer_approximate_tick_params(
      kClockFreqPeripheralHz  // device clock frequency
      ,
      kTickFreqHz  // desired counter frequency
      ,
      &rv_timer_tick_params  // pointer to output struct
      ));
  // Configure the tick params for a particular hart's counter
  CHECK_DIF_OK(dif_rv_timer_set_tick_params(
      &rv_timer, kHart  // hart to configure
      ,
      rv_timer_tick_params  // timing parameters struct
      ));

  uint64_t current_time;
  CHECK_DIF_OK(dif_rv_timer_counter_read(&rv_timer, kHart, &current_time));
  CHECK_DIF_OK(dif_rv_timer_arm(
      &rv_timer, kHart, kComparator,
      (current_time + kDeadline)  // go off when counter value is greater than
                                  // or equal to this value
      ));
  CHECK_DIF_OK(
      dif_rv_timer_counter_set_enabled(&rv_timer, kHart, kDifToggleEnabled));

  LOG_INFO("SW_INFO: RV Timer active");

  // ------------------------------------
  // Alert Ping

  // The ping timer will only ping alerts that have been enabled AND locked.
  // Therefore, it should be invoked after configuring and enabling each (local)
  // alert. The alert handler will regularly, at random intervals, ping alert
  // sources. If a source fails to respond, a local alert will be raised. The
  // ping timer won't start until configuration is locked.

  // 1. Connfig structs for all Incoming Alerts:
  //   (these alerts should never fire because we do not expect any incoming
  //   alerts)
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;  // each of the alerts is added to the list
    alert_classes[i] = kDifAlertHandlerClassA;  // configure them as Class A
  }

  // 2. Connfig structs for Local Alerts
  // Enable "alert ping fail" local alert and configure that to classb.
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail};
  dif_alert_handler_class_t loc_alert_classes[] = {
      kDifAlertHandlerClassB};  // configure them as Class B

  // 3. Connfig structs for Escalation phase
  dif_alert_handler_escalation_phase_t esc_phases[] = {{
      .phase = kDifAlertHandlerClassStatePhase0  // the phase this configuration
                                                 // describes
      ,
      .signal = 0  // the escalation signal that should be triggered when this
                   // phase begins
      ,
      .duration_cycles = 2000  // the duration of this phase, in cycles
  }};
  // Escalation protocol (struct) for an alert class
  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter =
          kDifToggleDisabled,  // Whether to automatically lock the accumulation
                               // counter
      .accumulator_threshold = UINT16_MAX,  // number of alerts that must fire
                                            // in order to trigger escalation
      .irq_deadline_cycles = UINT32_MAX,    // number of cycles this class's
                                            // associated IRQ handler has,
      //                                   // to acknowledge the IRQ, before
      //                                   escalation is triggered
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
      .alerts = alerts,  // list of alerts to configure
      .alert_classes =
          alert_classes,  // list of classes to assign each alert to
      .alerts_len = ARRAYSIZE(
          alerts),  // lengths of the arrays `alerts` and `alert_classes`
      .local_alerts = loc_alerts,  // list of local alerts to configure
      .local_alert_classes =
          loc_alert_classes,  // list of classes to assign each local alert to
      .local_alerts_len =
          ARRAYSIZE(loc_alerts),  // lengths of the arrays `local_alerts` and
                                  // `local_alert_classes`
      .classes = classes,         // list of alert classes to configure
      .class_configs = class_configs,  // list of alert class (escalation
                                       // protocol) configurations
      .classes_len = ARRAYSIZE(
          class_configs),  // length of the arrays `classes` and `class_configs`
      .ping_timeout =
          UINT16_MAX,  // ping timeout (16 bits) in cycles - max value to avoid
                       // timeout and consequent local alert
  };

  // 5. Configure Alerts
  // This also locks the configuration.
  // Once the configuration is locked, it cannot be reconfigured until after a
  // system reset.
  alert_handler_testutils_configure_all(
      &alert_handler, config,
      kDifToggleEnabled  // "Enable" to lock the configuration
  );

  // Checks whether alert handler's ping timer is locked
  bool is_locked;
  CHECK_DIF_OK(
      dif_alert_handler_is_ping_timer_locked(&alert_handler, &is_locked));
  CHECK(is_locked, "Expected alerts to be locked");

  LOG_INFO("SW_INFO: Alert ping is active");

  // ------------------------------------
  // PWM

  // Configuration struct for PWM general
  static const dif_pwm_config_t config_ = {
      .clock_divisor = 0,  // divisor that determines the period of a single
                           // "beat" within a PWM "pulse cycle".
      //                  // 0 = div by 1 (configures the "beat" period to the
      //                  core clock period)
      .beats_per_pulse_cycle = 32,  // total number of "beats" in a "pulse
                                    // cycle", including both "on" and "off"
  };

  // Configuration struct for a specific PWM channel
  static const dif_pwm_channel_config_t default_ch_cfg_ = {
      .duty_cycle_a =
          0,  // Primary duty cycle, in number of "beats" / "pulse cycle".
      .duty_cycle_b = 0,  // Secondary duty cycle, in number of "beats" / "pulse
                          // cycle" (only relevant in heartbeat and blink modes)
      .phase_delay = 0,   // Phase delay at the beginning of a "pulse cycle"
      .mode = kDifPwmModeFirmware,  // operation mode for this channel
      //                           // 0 = duty cycle set by by firmware and
      //                           remain constant
      //                           // 1 = duty cycle linearly sweeps between
      //                           primary and secondary
      //                           // 2 = duty cycle alternates between primary
      //                           and secondary
      .polarity = kDifPwmPolarityActiveHigh,  // polarity
      .blink_parameter_x = 0,  // only relevant for "Heartbeat" and "Blink"
      .blink_parameter_y = 0,  // only relevant for "Heartbeat" and "Blink"
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

  CHECK_DIF_OK(
      dif_pwm_configure(&pwm, config_));  // Configures "phase cycle" and "beat"
                                          // durations of all PWM channels

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
  // Set a connection between a MIO pad output and peripheral output
  // (this is so that the I/O pads will also toggle)
  for (int i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
    CHECK_DIF_OK(dif_pinmux_output_select(
        &pinmux, kPinmuxMioOut[i]  // Padring MIO output index
        ,
        kPinmuxOutsel[i]  // Peripheral output connection select
        ));
  }

  LOG_INFO("SW_INFO: PWM active");

  // ------------------------------------
  // OTP

  // Configure OTP Control to do periodic "consistency" & "integrity" checks.
  static const dif_otp_ctrl_config_t otp_ctrl_config = {
      .check_timeout = UINT32_MAX,  // timeout, in cycles, for an integrity or
                                    // consistency check to succeed
      //                                        // If an integrity or
      //                                        consistency check does not
      //                                        complete within the timeout
      //                                        window,
      //                                        // an error will be flagged in
      //                                        the !!STATUS register
      //                                        // an otp_error interrupt will
      //                                        be raised,
      //                                        // and an fatal_check_error
      //                                        alert will be sent out.
      //                                        // We don't want any of that in
      //                                        this test, so we use max timeout
      //                                        value.
      .integrity_period_mask = 0x1,  // Mask to limit the maximum period that
                                     // can be generated pseudo-randomly
      //                              // The pseudo-random period is generated
      //                              using a 40bit LFSR internally,
      //                              // This mask affects on the upper 32 bits
      //                              of the LFSR (lower 8 bits are not masked).
      //                              // A value of zero disables the periodic
      //                              check,
      //                              // Note: recommended real-life value is
      //                              0x3_FFFF, corresponding to a period of
      //                              ~2.8s at 24MHz.
      .consistency_period_mask = 0x1,  // Mask to limit the maximum period that
                                       // can be generated pseudo-randomly
      //                              // The pseudo-random period is generated
      //                              using a 40bit LFSR internally,
      //                              // This mask affects on the upper 32 bits
      //                              of the LFSR (lower 8 bits are not masked).
      //                              // A value of zero disables the periodic
      //                              check,
      //                              // Note: recommended real-life value is
      //                              0x3FF_FFFF, corresponding to a period of
      //                              ~716s at 24MHz.
  };

  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp_ctrl, otp_ctrl_config));

  LOG_INFO("SW_INFO: OTP periodic checks active");

  // ------------------------------------
  // AON Timer - activate in Watchdog mode (not wakeup mode) & IRQ
  static const uint64_t kTimeTillBark =
      1000;  // time in [us] - this is to reduce VCS run time of start-to-bark
             // to ~8 minutes

  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));  // AON timer, stop
  CHECK_DIF_OK(
      dif_aon_timer_clear_wakeup_cause(&aon_timer));  // AON timer, clear
  expected_isr_handler = wdog_irq_handler;
  nmi_fired = false;
  nmi_state = (dif_rv_core_ibex_nmi_state_t){0};
  CHECK_DIF_OK(dif_rv_core_ibex_enable_nmi(
      &rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));  // Enable WDOG NMI
  uint32_t count_cycles = aon_timer_testutils_get_aon_cycles_from_us(
      kTimeTillBark);  // translate to cycles
  aon_timer_testutils_watchdog_config(
      &aon_timer  // AON timer, activate
      ,
      count_cycles  // the number of AON clock cycles till barking (IRQ)
      ,
      UINT32_MAX  // the number of AON clock cycles till biting (Reset)
      ,
      false  // false = increment even while sleeping
  );

  LOG_INFO("SW_INFO: AON Timer active");

  // ------------------------------------
  LOG_INFO("SW_INFO: all H/W is active");
  test_status_set(0xff20);  // indicate S/W is idle
  CHECK_DIF_OK(dif_gpio_write(
      &gpio, 2, 1));  // Write to set IOA2 high at the start of the power state
  wait_for_interrupt();  // execute "wfi" instruction

  // Note, if running on DV environment:
  // We wait here for the AON Timer to issue an NMI.
  // This will make the S/W exit with "true" and the Verilog test to finish with
  // "pass". Without this, the CPU will remain idle and the simulator will end
  // the test (due to simulation timeout) with "fail".

  CHECK_DIF_OK(dif_gpio_write(
      &gpio, 2, 0));  // Write to set IOA2 low at the end of the power state

  // ------------------------------------
  // Prepare to exit

  // We expect the watchdog bark interrupt to be pending on the peripheral side.
  CHECK(irq_is_pending, "Expected watchdog bark interrupt to be pending");

  // Check NMI previous state (before clearing):
  CHECK(nmi_state.wdog_enabled && nmi_state.wdog_barked,  // enabled & barked
        "WDOG NMI state check1 not expected! wdog_enable:%x, wdog_raised:%x",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);

  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex,
      (dif_rv_core_ibex_nmi_state_t *)&nmi_state));  // get the current state
  // Check NMI current state (after clearing):
  CHECK(nmi_state.wdog_enabled && !nmi_state.wdog_barked,  // enabled & cleared
        "WDOG NMI state check2 not expected! wdog_enable:%x wdog_raised:%x",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);

  // Check that no external interrupts have occurred.
  CHECK(ext_irq_fired == false, "Unexpected external interrupt triggered.");

  // Check that the system has not been reset due to escalation
  // and that the reset reason is still POR.
  pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0);

  aon_timer_testutils_shutdown(&aon_timer);  // turn-off the AON timer hardware

  // Set the test status flag back to "TestStatusInTest"
  // This is required because the OpenTitan Test Framework (OTTF) will fail the
  // test if we transition to "TestStatusPassed" state from a state other than
  // "TestStatusInTest" (see:
  // $REPO_TOP//hw/dv/sv/sw_test_status/sw_test_status_if.sv)
  test_status_set(kTestStatusInTest);

  LOG_INFO("SW_INFO: exitting");
  return true;
}
