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
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
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

/**
 * A utility function to wait enough until the alert handler pings a peripheral
 * alert
 */
void wait_enough_for_alert_ping(void) {
  // wait enough
  if (kDeviceType == kDeviceFpgaCw310) {
    // 2*margin_of_safety*(2**DW)*(1/kClockFreqPeripheralHz)
    // 2*4*(2**16)*(400ns) = 0.2s
    busy_spin_micros(1000 * 200);
  } else if (kDeviceType == kDeviceSimDV) {
    // NUM_ALERTS*2*margin_of_safety*(2**DW)*(1/kClockFreqPeripheralHz)
    // 2*4*(2**3)*(40ns) = 3us
    busy_spin_micros(3);
  } else {
    // Verilator
    // 2*margin_of_safety*(2**DW)*(1/kClockFreqPeripheralHz)
    // 2*4*(2**16)*(8us) = 4s
    // This seems to be impractical for the current clock frequency config
    // of the Verilator tests (kClockFreqPeripheralHz = 125K).
    LOG_FATAL("SUPPORTED PLATFORMS: DV and FPGA");
    LOG_FATAL("TO SUPPORT THE PLATFORM %d, COMPUTE THE RIGHT WAIT-TIME",
              kDeviceType);
  }
}

// NVM counters/fields to keep test steps between deep sleep modes
enum {
  // The counter ID for the non-volatile counter keeping the test steps.
  kCounterTestSteps = 0,
  // The counter ID for the non-volatile counter keeping num_iters for each
  // test phase.
  kCounterTestPhase = 1,
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

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 10000,
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
  for (dif_alert_handler_local_alert_t i = 0; i < 7; i++) {
    CHECK_DIF_OK(dif_alert_handler_local_alert_acknowledge(&alert_handler, i));
  }
}

/**
 * Counts and returns the number of fired alerts
 */
static uint16_t alert_handler_num_fired_alerts(void) {
  bool is_cause;
  // Indicates if any of the alerts or local alerts is fired.
  uint16_t accumulator = 0;
  // Loop over all alert_cause regs
  for (size_t alert = 0; alert < ALERT_HANDLER_PARAM_N_ALERTS; alert++) {
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, alert, &is_cause));
    accumulator += is_cause;
  }
  return accumulator;
}

/**
 * Counts and returns the number of fired loc_alerts
 */
static uint16_t alert_handler_num_fired_loc_alerts(void) {
  bool is_cause;
  // Indicates if any of the alerts or local alerts is fired.
  uint16_t accumulator = 0;
  // Loop over all loc_alert_cause regs
  // Keep the result for kDifAlertHandlerLocalAlertAlertPingFail in a seperate
  // variable
  for (dif_alert_handler_local_alert_t i = 0; i < 7; i++) {
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
 * Verifies that wakeup source is the AON timer
 * (kDifPwrmgrWakeupRequestSourceFive).
 */
static void check_wakeup_reason(void) {
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(
            &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) == true,
        "wakeup reason wrong exp:%d  obs:%d", kDifPwrmgrWakeupRequestSourceFive,
        wakeup_reason);
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
static uint32_t rnd_num_iterations;
// To keep track of the test steps
static size_t test_step_cnt;

/**
 * Helper function to keep the test body clean
 * Initializes the flash_ctrl and test counters.
 * This is called once per reset.
 */
void init_test_components(void) {
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
}

/**
 * Execute the test phases:
 * Phase #1: Check if sleep/wakeup causes any spurious alerts
 * Phase #2: Check if the ping mechanism keep working after sleep/wakeup cycles
 */
static void execute_test_phases(uint8_t test_phase, uint32_t ping_timeout_cyc) {
  // To keep the test results
  bool is_cause;
  bool is_locked;
  bool sleep_mode;
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
    // Initialize the counters.
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterTestSteps));
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterTestPhase));
    // set num_iterations to a random value between 4 and 8
    rand_testutils_reseed();
    rnd_num_iterations = rand_testutils_gen32_range(4, 8);
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_set(kCounterTestPhase, rnd_num_iterations));
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterTestSteps, &test_step_cnt));

    // Set the AON timer to send a wakeup signal in ~10-20us.
    CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(
        &aon_timer, rand_testutils_gen32_range(2, 4)));
    // Enter normal sleep mode.
    enter_low_power(/*deep_sleep=*/false);
  } else { /*wakeup reset*/
    LOG_INFO("Test phase = %d, test step = %d", test_phase, test_step_cnt);
    // Check the wakeup reason and do the cleanup
    check_wakeup_reason();
    cleanup_wakeup_src();

    // Check if handler is locked after waking up from normal sleep.
    CHECK_DIF_OK(
        dif_alert_handler_is_ping_timer_locked(&alert_handler, &is_locked));
    CHECK(
        is_locked,
        "The alert handler should be locked after waking up from normal sleep");

    // Check if sleep/wakeup cycle caused any spurious alerts.
    //
    // Phase#1: No alerts or loc_alerts shall be fired
    // `ping_timeout_cnt = 256`. End the test if any alerts or loc_alerts is
    // fired.
    //
    // Phase #2: N/A (As the `ping_timeout_cnt = 2` in this phase, the ping-fail
    // alerts will come continuosly)
    num_fired_alerts = alert_handler_num_fired_alerts();
    num_fired_loc_alerts = alert_handler_num_fired_loc_alerts();
    if (test_phase == 1) {
      // No alerts is expected to fire
      CHECK(num_fired_alerts == 0, "Phase #1: Expected_num_fired_alerts is 0");
      CHECK(num_fired_loc_alerts == 0,
            "Phase #1: Expected_num_fired_loc_alerts is 0");
    }

    // Check that ping mechanism still works as expected after sleep/wakeup
    // cycle
    //
    // Phase #1: No alerts or loc_alerts shall be fired
    //
    // Phase #2: new alerts shall be fired
    // Phase #2: `kDifAlertHandlerLocalAlertAlertPingFail` shall be fired
    // Phase #2: `kDifAlertHandlerLocalAlertEscalationPingFail` shall be fired.
    if (test_phase == 1) {
      // Wait for new pings
      wait_enough_for_alert_ping();

      CHECK(alert_handler_num_fired_alerts() == 0,
            "Phase #1: Expected_num_fired_alerts is 0");
      CHECK(alert_handler_num_fired_loc_alerts() == 0,
            "Phase #1: Expected_num_fired_loc_alerts is 0");
    } else if (test_phase == 2) {
      // Clear local_alert_cause and alert_cause regs for a clean start
      // to test the ping-fail mechanism.
      alert_handler_clear_cause_regs();

      // Wait for new pings
      wait_enough_for_alert_ping();

      CHECK(alert_handler_num_fired_alerts() > 0,
            "Phase #2: No new alerts has been fired after wakeup!");
      CHECK(alert_handler_num_fired_loc_alerts() == 2,
            "Phase #2: Only 2 loc_alerts (esc-ping-fail, alert-ping-fail) "
            "should be fired!");
      CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
          &alert_handler, kDifAlertHandlerLocalAlertAlertPingFail, &is_cause));
      CHECK(is_cause,
            "Phase #2: kDifAlertHandlerLocalAlertAlertPingFail must have been "
            "fired");
      CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
          &alert_handler, kDifAlertHandlerLocalAlertEscalationPingFail,
          &is_cause));
      CHECK(is_cause,
            "Phase #2: kDifAlertHandlerLocalAlertEscalationPingFail must have "
            "been fired");
    } else {
      LOG_FATAL("WRONG TEST PHASE!!");
    }

    // Increment the test_step counter for the next test step
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterTestSteps));
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterTestSteps, &test_step_cnt));

    // Set the AON timer to send a wakeup signal in ~100-150us.
    CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(
        &aon_timer, rand_testutils_gen32_range(20, 30)));

    // Enter the normal sleep or deep sleep mode
    // Deep sleep mode is time consuming in DV, and normal sleep mode is more
    // important for the test. Therefore, the test goes to the deep sleep mode
    // only once while transitioning from phase #1 to phase #2.
    sleep_mode = (test_step_cnt == rnd_num_iterations);
    enter_low_power(/*deep_sleep=*/sleep_mode);
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

/**
 * Resets the chip.
 */
static void chip_sw_reset(void) {
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  busy_spin_micros(100);
  CHECK(false, "Should have reset before this line");
}

bool test_main(void) {
  init_test_components();

  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  if (rst_info & kDifRstmgrResetInfoPor) {
    // Power-on reset
    //  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("POR reset");
    // Initialize the counters.
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterTestSteps));
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterTestPhase));
    // set num_iterations to a random value between 4 and 8
    rand_testutils_reseed();
    rnd_num_iterations = rand_testutils_gen32_range(4, 8);
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_set(kCounterTestPhase, rnd_num_iterations));
    LOG_INFO("Will run %d iterations per phase", rnd_num_iterations);
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterTestSteps, &test_step_cnt));

    // We need to initialize the info FLASH partitions storing the Creator and
    // Owner secrets to avoid getting the flash controller into a fatal error
    // state.
    if (kDeviceType == kDeviceFpgaCw310) {
      CHECK_STATUS_OK(keymgr_testutils_flash_init(&flash_ctrl, &kCreatorSecret,
                                                  &kOwnerSecret));
      chip_sw_reset();
    }
  }
  CHECK_STATUS_OK(
      ret_sram_testutils_counter_get(kCounterTestPhase, &rnd_num_iterations));
  CHECK_STATUS_OK(
      ret_sram_testutils_counter_get(kCounterTestSteps, &test_step_cnt));

  // TEST PHASE #1 (ping-timeout = 256)
  // To ensure that the ping mechanism won't send spurious failure.
  // No alert or local_alert is expected to be fired.
  while (test_step_cnt < rnd_num_iterations) {
    execute_test_phases(/*test_phase=*/1, /*ping_timeout_cyc=*/256);
  }

  // TEST PHASE #2: ping_timeout = 1
  // To ensure that ping mechanism will continue to send out pings after wakeup
  // At least one of the alerts should cause a ping_timeout_fail event after
  // wakeup.
  while (test_step_cnt <= 2 * rnd_num_iterations) {
    execute_test_phases(/*test_phase=*/2, /*ping_timeout_cyc=*/1);
  }

  // Do the cleanup
  cleanup_wakeup_src();

  return true;
}
