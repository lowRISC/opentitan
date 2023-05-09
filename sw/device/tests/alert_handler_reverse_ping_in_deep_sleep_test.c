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
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  // This time needs to be greater than 0.175s. See test plan for more details.
  kTestParamWakeupThresholdUsec = 200000,

  // This time is needed to cycle through all the alert pings. See test plan
  // for more details.
  kTestParamCycleThroughAllPingsUsec = kTestParamWakeupThresholdUsec >> 2,
  kTestParamAlertHandlerIrqDeadlineUsec = 100,
  kTestParamAlertHandlerPhase0EscalationDurationUsec = 100,
  kTestParamAlertHandlerPingTimeoutUsec = 20,
};

static_assert(
    kTestParamWakeupThresholdUsec > 175000,
    "Invalid kTestParamWakeupThresholdUsec. See test plan for more details.");

static dif_flash_ctrl_state_t flash_ctrl;
static dif_rv_plic_t plic;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_aon_timer_t aon_timer;
static dif_alert_handler_t alert_handler;
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static volatile bool interrupt_serviced = false;

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Enable all the alert_handler interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);
}

/**
 * Program the alert handler to escalate on alerts upto phase 1 (i.e. wipe
 * secret) but not trigger reset. Then CPU can check if the correct interrupt
 * fires and check the local alert cause register.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all incoming alerts and configure them to classa.
  // This alert should never fire because we do not expect any incoming alerts.
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // Enable alert ping fail local alert and configure that to classb.
  dif_alert_handler_local_alert_t loc_alerts[ALERT_HANDLER_PARAM_N_LOC_ALERT];
  dif_alert_handler_class_t loc_alert_classes[ALERT_HANDLER_PARAM_N_LOC_ALERT];
  for (dif_alert_handler_local_alert_t i = 0;
       i < ALERT_HANDLER_PARAM_N_LOC_ALERT; ++i) {
    loc_alerts[i] = i;
    loc_alert_classes[i] = kDifAlertHandlerClassB;
  }
  uint32_t cycles = 0;
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kTestParamAlertHandlerPhase0EscalationDurationUsec, &cycles));
  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {
          .phase = kDifAlertHandlerClassStatePhase0,
          .signal = 0,
          .duration_cycles = cycles,
      },
  };

  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kTestParamAlertHandlerIrqDeadlineUsec, &cycles));
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
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kTestParamAlertHandlerPingTimeoutUsec, &cycles));
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
      .ping_timeout = cycles,
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
 * Ensure there were no local alerts fired.
 */
static void check_local_alerts(void) {
  for (dif_alert_handler_local_alert_t i = 0;
       i < ALERT_HANDLER_PARAM_N_LOC_ALERT; ++i) {
    bool is_cause;
    CHECK_DIF_OK(
        dif_alert_handler_local_alert_is_cause(&alert_handler, i, &is_cause));
    CHECK(!is_cause, "Unexpected local alert cause: %d", i);
  }
}

/**
 * Resets the chip.
 */
static void chip_sw_reset(void) {
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  busy_spin_micros(100);
  CHECK(false, "Should have reset before this line");
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) { interrupt_serviced = true; }

bool test_main(void) {
  init_peripherals();

  // We need to initialize the info FLASH partitions storing the Creator and
  // Owner secrets to avoid getting the flash controller into a fatal error
  // state.
  if (kDeviceType == kDeviceFpgaCw310) {
    dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
    if (rst_info & kDifRstmgrResetInfoPor) {
      CHECK_STATUS_OK(keymgr_testutils_flash_init(&flash_ctrl, &kCreatorSecret,
                                                  &kOwnerSecret));
      chip_sw_reset();
    }
  }

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    LOG_INFO("POR reset");

    dif_rstmgr_reset_info_t reset_info = kDifRstmgrResetInfoPor;

    // Update the expected `reset_info` value for the FPGA target, as we have
    // a soft reset required to apply the info flash page configuration.
    if (kDeviceType == kDeviceFpgaCw310) {
      reset_info = kDifRstmgrResetInfoSw;
    }

    CHECK(UNWRAP(rstmgr_testutils_reset_info_any(&rstmgr, reset_info)));
    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

    alert_handler_config();

    irq_global_ctrl(true);
    irq_external_ctrl(true);

    uint32_t wakeup_threshold = 0;
    CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(
        kTestParamWakeupThresholdUsec, &wakeup_threshold));

    // Sleep longer in FPGA and silicon targets.
    if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
      uint32_t wakeup_threshold_new = wakeup_threshold * 50;
      CHECK(wakeup_threshold_new > wakeup_threshold,
            "Detected wakeup_threshold overflow.");
      wakeup_threshold = wakeup_threshold_new;
    }

    // Wait for the alert handler to cycle through all pings and make sure
    // there were no interrupts fired during that time.
    busy_spin_micros(kTestParamCycleThroughAllPingsUsec);
    check_local_alerts();
    CHECK(interrupt_serviced == false, "Unexpected interrupt triggered.");

    // Enable and enter deep sleep.
    CHECK_STATUS_OK(
        aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold));
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceFive, 0));
    wait_for_interrupt();
    CHECK(false, "Fail to enter in low power mode!");
    OT_UNREACHABLE();
  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) == true) {
    LOG_INFO("Wakeup reset");
    CHECK(UNWRAP(rstmgr_testutils_is_reset_info(
        &rstmgr, kDifRstmgrResetInfoLowPowerExit)));
    CHECK_STATUS_OK(aon_timer_testutils_shutdown(&aon_timer));

    // At this point the test has verified that the reset reason is low power
    // exit, which discounts any resets triggered by local alert escalations.
    // We check local alerts and interrupt flag one more time to ensure the
    // alert handler resumes with the expected state.
    check_local_alerts();
    CHECK(interrupt_serviced == false, "Unexpected interrupt triggered.");
    return true;
  }
  dif_pwrmgr_wakeup_reason_t wakeup_reason;
  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
  LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
            wakeup_reason.types, wakeup_reason.request_sources);
  return false;
}
