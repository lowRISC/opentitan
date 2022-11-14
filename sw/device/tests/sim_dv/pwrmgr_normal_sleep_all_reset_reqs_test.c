// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();
static volatile const uint8_t RST_IDX[7] = {0, 1, 2, 3, 4, 5, 6};
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

/**
 * Objects to access the peripherals used in this test via dif API.
 */
static dif_flash_ctrl_state_t flash_ctrl;
static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_sysrst_ctrl_t sysrst_ctrl_aon;
static dif_rstmgr_t rstmgr;

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset) but
 * the phase 1 (i.e. wipe secrets) should occur and last during the time the
 * wdog is programed to bark.
 *
 * Notice these settings are suitable for sim_dv. For other platforms we scale
 * the resulting cycles by a factor of 10.
 */
enum {
  kWdogBarkMicros = 3 * 100,          // 300 us
  kWdogBiteMicros = 4 * 100,          // 400 us
  kEscalationPhase0Micros = 1 * 100,  // 100 us
  // The cpu value is slightly larger to avoid flakey results.
  kEscalationPhase0MicrosCpu = kEscalationPhase0Micros + 20,  // 120 us
  kEscalationPhase1Micros = 5 * 100,                          // 500 us
  kEscalationPhase2Micros = 50,                               // 50 us
};

static_assert(
    kWdogBarkMicros < kWdogBiteMicros &&
        kWdogBarkMicros > kEscalationPhase0Micros &&
        kWdogBarkMicros < (kEscalationPhase0Micros + kEscalationPhase1Micros) &&
        kWdogBiteMicros < (kEscalationPhase0Micros + kEscalationPhase1Micros),
    "The wdog bark and bite shall happens during the escalation phase 1");

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral;
  dif_rv_plic_irq_id_t irq_id;
  uint32_t irq = 0;
  uint32_t alert = 0;

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq =
        (dif_aon_timer_irq_t)(irq_id -
                              (dif_rv_plic_irq_id_t)
                                  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    // Stops escalation process.
    CHECK_DIF_OK(dif_alert_handler_escalation_clear(&alert_handler,
                                                    kDifAlertHandlerClassA));
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));

    CHECK(irq != kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark,
          "AON Timer Wdog should not bark");

  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    irq = (dif_aon_timer_irq_t)(irq_id -
                                (dif_rv_plic_irq_id_t)
                                    kTopEarlgreyPlicIrqIdAlertHandlerClassa);

    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler, alert));

    dif_alert_handler_class_state_t state;
    CHECK_DIF_OK(dif_alert_handler_get_class_state(
        &alert_handler, kDifAlertHandlerClassA, &state));

    CHECK(state == kDifAlertHandlerClassStatePhase0, "Wrong phase %d", state);

    CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
}

/**
 * Initialize the peripherals used in this test.
 */
void init_peripherals(void) {
  // Initialize pwrmgr.
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize sysrst_ctrl.
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl_aon));

  // Initialize rstmgr to check the reset reason.
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Initialize aon timer to use the wdog.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  // Initialize flash_ctrl
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize plic.
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // Initialize alert handler.
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
}

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset) but
 * the phase 1 (i.e. wipe secrets) should occur and last during the time the
 * wdog is programed to bark.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[] = {kTopEarlgreyAlertIdPwrmgrAonFatalFault};
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassA};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase0Micros) *
           alert_handler_testutils_cycle_rescaling_factor()},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase1Micros) *
           alert_handler_testutils_cycle_rescaling_factor()},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase2Micros) *
           alert_handler_testutils_cycle_rescaling_factor()}};

  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = alert_handler_testutils_get_cycles_from_us(10) *
                             alert_handler_testutils_cycle_rescaling_factor(),
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

  alert_handler_testutils_configure_all(&alert_handler, config,
                                        kDifToggleEnabled);
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
}

/**
 * Execute the aon timer interrupt test.
 */
static void config_escalate(dif_aon_timer_t *aon_timer,
                            const dif_pwrmgr_t *pwrmgr) {
  uint64_t bark_cycles =
      udiv64_slow(kWdogBarkMicros * kClockFreqAonHz, 1000000, NULL) *
      alert_handler_testutils_cycle_rescaling_factor();
  uint64_t bite_cycles =
      udiv64_slow(kWdogBiteMicros * kClockFreqAonHz, 1000000, NULL) *
      alert_handler_testutils_cycle_rescaling_factor();

  CHECK(bite_cycles < UINT32_MAX,
        "The value %u can't fit into the 32 bits timer counter.", bite_cycles);

  LOG_INFO(
      "Wdog will bark after %u/%u us/cycles and bite after %u/%u us/cycles",
      (uint32_t)kWdogBarkMicros, (uint32_t)bark_cycles,
      (uint32_t)kWdogBiteMicros, (uint32_t)bite_cycles);

  // Setup the wdog bark and bite timeouts.
  aon_timer_testutils_watchdog_config(aon_timer, bark_cycles, bite_cycles,
                                      false);

  // Trigger the alert handler to escalate.
  dif_pwrmgr_alert_t alert = kDifPwrmgrAlertFatalFault;
  CHECK_DIF_OK(dif_pwrmgr_alert_force(pwrmgr, alert));
}

/**
 * Configure the sysrst.
 */
static void config_sysrst(const dif_pwrmgr_t *pwrmgr,
                          const dif_sysrst_ctrl_t *sysrst_ctrl_aon) {
  LOG_INFO("sysrst enabled");

  // Set sysrst as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceOne,
                                              kDifToggleEnabled));
  LOG_INFO("Reset Request SourceOne is set");

  // Configure sysrst key combo
  // reset pulse : 50 us
  // detect durration : 50 us

  dif_sysrst_ctrl_key_combo_config_t sysrst_ctrl_key_combo_config = {
      .keys = kDifSysrstCtrlKeyAll,
      .detection_time_threshold = 10,
      .actions = kDifSysrstCtrlKeyComboActionAll,
      .embedded_controller_reset_duration = 10};

  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      sysrst_ctrl_aon, kDifSysrstCtrlKeyCombo0, sysrst_ctrl_key_combo_config));
  // Configure sysrst input change
  // debounce durration : 100 us
  dif_sysrst_ctrl_input_change_config_t sysrst_ctrl_input_change_config = {
      .input_changes = kDifSysrstCtrlInputAll, .debounce_time_threshold = 20};

  // Configure pinmux
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      sysrst_ctrl_aon, sysrst_ctrl_input_change_config));

  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
      kTopEarlgreyPinmuxInselIor13));
}

static void normal_sleep_sysrst(const dif_pwrmgr_t *pwrmgr) {
  // Place device into low power and immediately wake.
  dif_pwrmgr_domain_config_t config;
  config = kDifPwrmgrDomainOptionUsbClockInLowPower |
           kDifPwrmgrDomainOptionCoreClockInLowPower |
           kDifPwrmgrDomainOptionIoClockInLowPower |
           kDifPwrmgrDomainOptionMainPowerInLowPower;
  pwrmgr_testutils_enable_low_power(pwrmgr, kDifPwrmgrWakeupRequestSourceOne,
                                    config);
  LOG_INFO("Normal sleep set for sysrst");

  // Enter in low power mode.
  wait_for_interrupt();
}

static void timer_on(uint32_t usec) {
  busy_spin_micros(usec);
  // If we arrive here the test must fail.
  CHECK(false, "Timeout waiting for reset!");
}

/**
 * Configure the wdog.
 */
static void config_wdog(const dif_aon_timer_t *aon_timer,
                        const dif_pwrmgr_t *pwrmgr, uint64_t bark_time_us,
                        uint64_t bite_time_us) {
  uint32_t bark_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(bark_time_us);
  uint32_t bite_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(bite_time_us);

  LOG_INFO("Wdog will bark after %u us and bite after %u us",
           (uint32_t)bark_time_us, (uint32_t)bite_time_us);
  // Setup the wdog bark and bite timeouts.
  aon_timer_testutils_watchdog_config(aon_timer, bark_cycles, bite_cycles,
                                      false);
  // Set wdog as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
}

/**
 * Execute the aon timer wdog bite reset test.
 */
static void wdog_bite_test(const dif_aon_timer_t *aon_timer,
                           const dif_pwrmgr_t *pwrmgr, uint64_t bark_time_us) {
  uint64_t bite_time_us = bark_time_us * 2;
  config_wdog(aon_timer, pwrmgr, bark_time_us, bite_time_us);

  // The `intr_state` takes 3 aon clock cycles to rise plus 2 extra cycles as a
  // precaution.
  uint32_t wait_us =
      bark_time_us +
      udiv64_slow(5 * 1000000 + kClockFreqAonHz - 1, kClockFreqAonHz, NULL);

  // Wait bark time and check that the bark interrupt requested.
  busy_spin_micros(wait_us);
  bool is_pending = false;
  CHECK_DIF_OK(dif_aon_timer_irq_is_pending(
      aon_timer, kDifAonTimerIrqWdogTimerBark, &is_pending));
  CHECK(is_pending, "Wdog bark irq did not rise after %u microseconds",
        wait_us);

  // Wait for the remaining time to the wdog bite.
  busy_spin_micros(wait_us);
  // If we arrive here the test must fail.
  CHECK(false, "Timeout waiting for Wdog bite reset!");
}

/**
 * Execute the aon timer wdog bite reset during sleep test.
 */
static void sleep_wdog_bite_test(const dif_aon_timer_t *aon_timer,
                                 const dif_pwrmgr_t *pwrmgr,
                                 uint64_t bark_time_us) {
  uint64_t bite_time_us = bark_time_us * 2;
  config_wdog(aon_timer, pwrmgr, bark_time_us, bite_time_us);
}

static void normal_sleep_wdog(const dif_pwrmgr_t *pwrmgr) {
  // Place device into low power and immediately wake.
  dif_pwrmgr_domain_config_t config;
  config = kDifPwrmgrDomainOptionUsbClockInLowPower |
           kDifPwrmgrDomainOptionCoreClockInLowPower |
           kDifPwrmgrDomainOptionIoClockInLowPower |
           kDifPwrmgrDomainOptionMainPowerInLowPower;

  // Enter in low power mode.
  pwrmgr_testutils_enable_low_power(pwrmgr, kDifPwrmgrWakeupRequestSourceTwo,
                                    config);
  LOG_INFO("Normal sleep set for watchdog");
  wait_for_interrupt();
}

static void normal_sleep_por(const dif_pwrmgr_t *pwrmgr) {
  // Set por as a reset source.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));

  // Place device into low power and immediately wake.
  dif_pwrmgr_domain_config_t config;
  config = kDifPwrmgrDomainOptionUsbClockInLowPower |
           kDifPwrmgrDomainOptionCoreClockInLowPower |
           kDifPwrmgrDomainOptionIoClockInLowPower |
           kDifPwrmgrDomainOptionMainPowerInLowPower;

  // Program the pwrmgr to go to deep sleep state (clocks off).
  pwrmgr_testutils_enable_low_power(
      pwrmgr,
      (kDifPwrmgrWakeupRequestSourceOne | kDifPwrmgrWakeupRequestSourceTwo |
       kDifPwrmgrWakeupRequestSourceThree | kDifPwrmgrWakeupRequestSourceFour |
       kDifPwrmgrWakeupRequestSourceFive | kDifPwrmgrWakeupRequestSourceSix),
      config);
  LOG_INFO("ready for pad por");
  // Enter in low power mode.
  wait_for_interrupt();
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_peripherals();

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);

  alert_handler_config();

  // First check the flash stored value
  uint32_t event_idx = flash_ctrl_testutils_counter_get(0);

  // Enable flash access
  flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                             /*rd_en*/ true,
                                             /*prog_en*/ true,
                                             /*erase_en*/ true,
                                             /*scramble_en*/ false,
                                             /*ecc_en*/ false,
                                             /*he_en*/ false);

  // Increment flash counter to know where we are
  flash_ctrl_testutils_counter_increment(&flash_ctrl, 0);

  LOG_INFO("Test round %d", event_idx);
  LOG_INFO("RST_IDX[%d] = %d", event_idx, RST_IDX[event_idx]);

  // Check if there was a HW reset caused by expected cases
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoSysRstCtrl ||
            rst_info == kDifRstmgrResetInfoWatchdog ||
            rst_info == kDifRstmgrResetInfoEscalation ||
            rst_info == kDifRstmgrResetInfoLowPowerExit ||
            rst_info == (kDifRstmgrResetInfoSysRstCtrl |
                         kDifRstmgrResetInfoLowPowerExit) ||
            rst_info ==
                (kDifRstmgrResetInfoPor | kDifRstmgrResetInfoLowPowerExit) ||
            rst_info == (kDifRstmgrResetInfoWatchdog |
                         kDifRstmgrResetInfoLowPowerExit) ||
            rst_info == (kDifRstmgrResetInfoEscalation |
                         kDifRstmgrResetInfoLowPowerExit) ||
            rst_info == kDifRstmgrResetInfoSw,
        "Wrong reset reason %02X", rst_info);

  switch (RST_IDX[event_idx]) {
    case 0:
      LOG_INFO("Booting and setting normal sleep followed by sysrst");
      config_sysrst(&pwrmgr, &sysrst_ctrl_aon);
      normal_sleep_sysrst(&pwrmgr);
      timer_on(kWdogBiteMicros);
      break;
    case 1:
      LOG_INFO("Booting and setting normal sleep followed by hw por");
      normal_sleep_por(&pwrmgr);
      timer_on(kWdogBiteMicros);
      break;
    case 2:
      LOG_INFO(
          "Booting and setting normal sleep mode followed for low_power "
          "entry reset");
      LOG_INFO("Let SV wait timer reset");
      // actually the same test as normal sleep + watchdog
      rstmgr_testutils_pre_reset(&rstmgr);
      sleep_wdog_bite_test(&aon_timer, &pwrmgr, 200);
      normal_sleep_wdog(&pwrmgr);
      timer_on(kEscalationPhase0MicrosCpu);
      break;
    case 3:
      LOG_INFO(
          "Booting and setting normal sleep followed by watchdog reset "
          "combined "
          "with sw_req");
      LOG_INFO("Let SV wait timer reset");
      // Executing the wdog bite reset during sleep test.
      rstmgr_testutils_pre_reset(&rstmgr);

      // Assert reeset req
      CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
      LOG_INFO("Device reset from sw");
      sleep_wdog_bite_test(&aon_timer, &pwrmgr, 200);
      normal_sleep_wdog(&pwrmgr);
      timer_on(kEscalationPhase0MicrosCpu);
      break;
    case 4:
      LOG_INFO("Booting and setting normal sleep followed by watchdog reset");
      LOG_INFO("Let SV wait timer reset");
      // Executing the wdog bite reset during sleep test.
      rstmgr_testutils_pre_reset(&rstmgr);
      sleep_wdog_bite_test(&aon_timer, &pwrmgr, 200);
      normal_sleep_wdog(&pwrmgr);
      timer_on(kEscalationPhase0MicrosCpu);
      break;
    case 5:
      LOG_INFO("Booting and running normal sleep followed by escalation reset");
      LOG_INFO("Let SV wait timer reset");
      config_escalate(&aon_timer, &pwrmgr);
      timer_on(kEscalationPhase0MicrosCpu);
      break;
    case 6:
      LOG_INFO("Last Booting");
      // Turn off the AON timer hardware completely before exiting.
      aon_timer_testutils_shutdown(&aon_timer);
      return true;
      break;
    default:
      LOG_INFO("Booting for undefined case");
  }

  return false;
}
