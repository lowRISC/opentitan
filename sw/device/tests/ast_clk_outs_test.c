// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * AST CLK OUTPUTS TEST
 *
 * This test measure 3 clock outputs from ast (sys, io and usb)
 * by clkmgr frequency measurements.
 * Frequency meaasurement assumes aon_clk frequency 200KHz.
 * Given that, measurement is done for 500 us which is equivalent
 * to 100 measurements.
 * If measurement detects error (fast, slow), it will be stored
 * as recoverable error in clkmgr.
 *
 * After 100 measurements, test kicks in low-power mode, where
 * 3 clocks are off and measurement should not report spurious errors.
 * Wake up timer is set 500us which gives about 500us deep sleep.
 *
 * Then dut wakes up and repeat another 100 measurements before
 * test finish.
 *
 * Notice the test overrides the hardware behavior so it comes out with
 * calibrated USB clock, otherwise the USB clock frequency will be incorrect.
 * USB calibration should be a separate test, and may be vendor-specific.
 */
enum {
  kWaitForCSRPolling = 1,  // 1us
  // aon period : 5us
  // meaure for 100 of period
  kMeasurementDelayMicros = 500,
  // at lowpower mode, main/io/usb clocks are off after 40us
  kClockCoolDownTime = 40,
};
static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;

bool test_main(void) {
  dif_sensor_ctrl_t sensor_ctrl;
  dif_aon_timer_t aon_timer;

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR), &sensor_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  LOG_INFO("TEST: wait for ast init");
  dif_toggle_t init_st = kDifToggleDisabled;

  while (init_st == kDifToggleDisabled) {
    CHECK_DIF_OK(
        dif_sensor_ctrl_get_ast_init_done_status(&sensor_ctrl, &init_st));

    busy_spin_micros(kWaitForCSRPolling);
  }

  LOG_INFO("TEST: done ast init");

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    // At POR.
    LOG_INFO("Run clock measurements right after POR");
    clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
        &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
        /*low_speed=*/false);
    busy_spin_micros(kMeasurementDelayMicros);
    // check results
    clkmgr_testutils_check_measurement_counts(&clkmgr);
    clkmgr_testutils_disable_clock_counts(&clkmgr);

    // set wakeup timer to 500us to have enough down time
    // during the down time, all clock measurements are still enabled but
    // not suppose to report any errors
    uint32_t wakeup_threshold = kDeviceType == kDeviceSimVerilator ? 1000 : 100;
    aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold);
    // go to low power

    LOG_INFO("Start clock measurements right before deep sleep");
    clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
        &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
        /*low_speed=*/false);

    LOG_INFO("TEST: start deep low power mode");
    pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceFive,
        kDifPwrmgrDomainOptionUsbClockInActivePower);

    // Enter low power mode.
    LOG_INFO("TEST: Issue WFI to enter deep sleep");
    wait_for_interrupt();

  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) {
    // All clocks were inactive in low power, so wait some more so there are
    // enough AON cycles for measurements.
    busy_spin_micros(kMeasurementDelayMicros);
    clkmgr_testutils_check_measurement_counts(&clkmgr);
    LOG_INFO("TEST: disable clock measures");
    clkmgr_testutils_disable_clock_counts(&clkmgr);

    LOG_INFO("TEST: one more measurement");
    clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
        &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
        /*low_speed=*/false);
    busy_spin_micros(kMeasurementDelayMicros);
    clkmgr_testutils_check_measurement_counts(&clkmgr);
    clkmgr_testutils_disable_clock_counts(&clkmgr);

    LOG_INFO("TEST: done");
    return true;
  } else {  // error
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  return false;
}
