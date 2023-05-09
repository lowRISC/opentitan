// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwrmgr_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_rv_core_ibex_t ibex;
static dif_flash_ctrl_state_t flash_ctrl;

// This location will be update from SV to contain the expected alert.
static volatile const uint8_t kExpectedAlertNumber = 0;

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  // Initialize pwrmgr
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize aon_timer
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  mmio_region_t ibex_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(ibex_addr, &ibex));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
}

// NVM counters/fields to keep test steps between deep sleep modes
enum {
  // The counter ID for the non-volatile counter keeping the test steps.
  kCounterTestSteps = 0,
  // The counter ID for the non-volatile counter keeping the number of max
  // wakeup events
  kCounterMaxWakeups = 1,
};

/**
 * Program the alert handler to escalate on alerts upto phase 1 (i.e. wipe
 * secret) but not trigger reset. Then CPU can check if the correct interrupt
 * fires and check the local alert cause register.
 */
static void alert_handler_config(uint32_t ping_timeout) {
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all incoming alerts and configure them to classa.
  // This alert should never fire because we do not expect any incoming alerts.
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // Enable alert ping fail local alert and configure that to classb.
  // Enable other local alerts and configure them to classa.
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerLocalAlertAlertIntegrityFail,
      kDifAlertHandlerLocalAlertBusIntegrityFail,
      kDifAlertHandlerLocalAlertEscalationIntegrityFail,
      kDifAlertHandlerLocalAlertEscalationPingFail,
      kDifAlertHandlerLocalAlertShadowedStorageError,
      kDifAlertHandlerLocalAlertShadowedUpdateError};
  dif_alert_handler_class_t loc_alert_classes[] = {
      kDifAlertHandlerClassB, kDifAlertHandlerClassA, kDifAlertHandlerClassA,
      kDifAlertHandlerClassA, kDifAlertHandlerClassA, kDifAlertHandlerClassA,
      kDifAlertHandlerClassA};

  uint32_t cycles = 0;
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(200, &cycles));
  dif_alert_handler_escalation_phase_t esc_phases[] = {{
      .phase = kDifAlertHandlerClassStatePhase0,
      .signal = 0,
      .duration_cycles = cycles,
  }};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = cycles,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};
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
      .ping_timeout = ping_timeout,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
}

/**
 * Clear all alert_cause and local_alert_cause registers
 */
static void alert_handler_clear_cause_regs(void) {
  // Loop over all alert_cause regs
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; i++) {
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler, i));
  }

  // Loop over all loc_alert_cause regs
  for (dif_alert_handler_local_alert_t i = 0;
       i < ALERT_HANDLER_PARAM_N_LOC_ALERT; i++) {
    CHECK_DIF_OK(dif_alert_handler_local_alert_acknowledge(&alert_handler, i));
  }
}

/**
 * Checks if any of the alert_cause or local_alert_cause register is set
 * @param expected_alert_value: Expected value for the accumulator.
 */
static uint16_t alert_handler_num_fired_alerts(void) {
  bool is_cause;
  // Indicates if any of the alerts or local alerts is fired.
  uint16_t accumulator = 0;
  // Loop over all alert_cause regs
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; i++) {
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, i, &is_cause));
    if (is_cause) {
      LOG_INFO("Alert %d fired", i);
    }
    accumulator += is_cause;
  }
  return accumulator;
}

/**
 * Checks if any of the alert_cause or local_alert_cause register is set
 * @param expected_alert_value: Expected value for the accumulator.
 */
static uint16_t alert_handler_num_fired_loc_alerts(void) {
  bool is_cause;
  // Indicates if any of the alerts or local alerts is fired.
  uint16_t accumulator = 0;
  // Loop over all loc_alert_cause regs
  for (dif_alert_handler_local_alert_t i = 0;
       i < ALERT_HANDLER_PARAM_N_LOC_ALERT; i++) {
    CHECK_DIF_OK(
        dif_alert_handler_local_alert_is_cause(&alert_handler, i, &is_cause));
    accumulator += is_cause;
  }
  return accumulator;
}

/**
 * Configures the power manager and enter a sleep mode
 * @param deep_sleep: true => deep sleep, false => normal sleep
 */
static void enter_low_power(bool deep_sleep) {
  dif_pwrmgr_domain_config_t cfg;
  CHECK_DIF_OK(dif_pwrmgr_get_domain_config(&pwrmgr, &cfg));
  cfg = (cfg & (kDifPwrmgrDomainOptionIoClockInLowPower |
                kDifPwrmgrDomainOptionUsbClockInLowPower |
                kDifPwrmgrDomainOptionUsbClockInActivePower)) |
        (!deep_sleep ? kDifPwrmgrDomainOptionMainPowerInLowPower : 0);

  // Set the wake_up trigger as AON timer module
  // (kDifPwrmgrWakeupRequestSourceFive).
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, /*wake_up_request_source*/ kDifPwrmgrWakeupRequestSourceFive,
      cfg));
  wait_for_interrupt();
}

/**
 * Clean up wakeup sources.
 */
void cleanup_wakeup_src(void) {
  CHECK_DIF_OK(dif_aon_timer_wakeup_stop(&aon_timer));
  CHECK_DIF_OK(dif_aon_timer_clear_wakeup_cause(&aon_timer));
  // Ensure the de-asserted events have cleared from the wakeup pipeline
  // within 30us.
  busy_spin_micros(30);
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));
}

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

// To keep the random number of iterations
static uint32_t num_total_wakeups;
// To keep track of the test steps
static size_t test_step_cnt;

/**
 * Helper function to keep the test body clean
 * Initializes the flash_ctrl and test counters.
 */
void init_test_components() {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_peripherals();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Need a NVM counter to keep the test-step info
  // after waking up from the deep sleep mode.
  // Enable flash access
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));
  // Total number of iterations for each test phase
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterMaxWakeups, &num_total_wakeups));

  // We don't expect test_step_cnt to 256 (flash mem is filled with all zeros)
  // for this test. If it is 256, we just initialize the counters/NVM-fields
  // again.
  if (test_step_cnt == 256) {
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_init_zero(&flash_ctrl, kCounterTestSteps));
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_init_zero(&flash_ctrl,
                                                           kCounterMaxWakeups));
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterMaxWakeups,
                                                     &num_total_wakeups));
  }

  // If this is the first iteration,
  // set num_iterations to a random value between 8 and 32
  if (num_total_wakeups == 0) {
    // number of total wakeups
    num_total_wakeups = 2;
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
        &flash_ctrl, kCounterMaxWakeups, num_total_wakeups));
  }
}

/**
 * Execute the test phases:
 */
static void execute_test_phases(uint8_t test_phase, uint32_t ping_timeout_cyc) {
  // To keep the test results
  bool is_cause;
  bool is_locked;
  uint16_t num_fired_alerts;
  uint16_t num_fired_loc_alerts;

  // Need to configure the alert handler again after deep sleep
  CHECK_DIF_OK(
      dif_alert_handler_is_ping_timer_locked(&alert_handler, &is_locked));
  // Configure the alert handler after wakeup if necessary
  if (!is_locked) {
    alert_handler_config(/*ping_timeout=*/ping_timeout_cyc);
  }

  // Power-on reset
  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("POR reset");

    // Increment the test_step counter for the next test step
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_increment(&flash_ctrl, kCounterTestSteps));
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));

    // Set the AON timer to send a wakeup signal in ~10-50us.
    CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(
        &aon_timer, rand_testutils_gen32_range(2, 10)));

    // Trigger the SV side to inject fault.
    // DO NOT CHANGE THIS: it is used to notify the SV side.
    LOG_INFO("Ready for fault injection");

    // Enter normal sleep mode.
    enter_low_power(/*deep_sleep=*/false);
  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) ==
             true /*AON timer*/) {
    // Cleanup after wakeup
    cleanup_wakeup_src();

    // Check if handler is locked after waking up from normal sleep.
    CHECK_DIF_OK(
        dif_alert_handler_is_ping_timer_locked(&alert_handler, &is_locked));
    CHECK(
        is_locked,
        "The alert handler should be locked after waking up from normal sleep");

    // Clear all cause regs after the wakeup
    alert_handler_clear_cause_regs();

    // Wait for the fatal alert to trigger again
    busy_spin_micros(100);

    // The fatal alert fired by the SV
    LOG_INFO("Phase #1 step %d", test_step_cnt);
    LOG_INFO("Expected alert number = %d", kExpectedAlertNumber);

    num_fired_alerts = alert_handler_num_fired_alerts();
    num_fired_loc_alerts = alert_handler_num_fired_loc_alerts();
    LOG_INFO("num_fired alerts = %d, num_fired_loc_alerts = %d",
             num_fired_alerts, num_fired_loc_alerts);

    // Check if the number of the fired alerts/local-alerts are correct
    CHECK(num_fired_alerts == 1,
          "Phase #1: Only a single alert must be fired after wakeup!");
    CHECK(num_fired_loc_alerts == 0,
          "Phase #1: No local alerts must be fired!");

    // Check if the expected fatal alert has been fired.
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, kExpectedAlertNumber, &is_cause));
    CHECK(is_cause, "Phase #1: Expected alert has NOT been fired!!");

    // Increment the test_step counter for the next test step
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_increment(&flash_ctrl, kCounterTestSteps));
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));

    // Set the AON timer to send a wakeup signal in ~10-50us.
    CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(
        &aon_timer, rand_testutils_gen32_range(2, 10)));
    // Enter the normal sleep mode
    enter_low_power(/*deep_sleep=*/false);
  } else {
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup_reason=%x", wakeup_reason);
    CHECK(false, "Unexpected wakeup reason");
  }
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

bool test_main(void) {
  init_test_components();

  // TEST PHASE #1 (ping-timeout = 256)
  // To ensure that fatal alerts keep firing after sleep/wakeup.
  // Only a single fatal alert is expected to be fired.
  // No local alerts is expected to be fired.
  while (test_step_cnt < num_total_wakeups) {
    // TODO: It seems to be that the only way to continue the SW execution
    // after a kTopEarlgreyAlertIdFlashCtrlFatalStdErr or
    // kTopEarlgreyAlertIdSramCtrlMainFatalError a reset. In this test, we are
    // only interested in the shallow sleep mode. Figure out a method to handle
    // those alerts in C code. Currently, they are bypassed by the SV through
    // aplusarg (avoid_inject_fatal_error_for_ips).
    execute_test_phases(/*test_phase=*/1, /*ping_timeout_cyc=*/256);
  }

  // Do the cleanup
  cleanup_wakeup_src();

  return true;
}
