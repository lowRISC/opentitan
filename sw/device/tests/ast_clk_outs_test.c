// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/sensor_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * AST CLK OUTPUTS TEST
 *
 * This test measures clock counts with clkmgr frequency measurements,
 * performing 100 measurements per round. Measurement errors (fast or slow
 * clocks) are recorded as recoverable error in clkmgr.
 *
 * After 100 measurements, this configures the clock counters per external
 * clock and low speed settings before entering low-power mode, where all but
 * the aon clock are off. The expectation is that main and io clocks will
 * report errors, but div2 and div4 should not.
 *
 * When the dut wakes up, another 100 measurements are done before the
 * test finishes.
 *
 * Notice the test overrides the hardware behavior so it comes out with
 * calibrated USB clock, otherwise the USB clock frequency will be incorrect.
 * USB calibration should be a separate test, and may be vendor-specific.
 */
enum {
  kWaitForCSRPollingUs = 1,  // 1us
  kMeasurementsPerRound = 100,
};

static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;

bool test_main(void) {
  dif_sensor_ctrl_t sensor_ctrl;
  dif_aon_timer_t aon_timer;

  uint32_t delay_micros = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_us_from_aon_cycles(
      kMeasurementsPerRound, &delay_micros));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR),
      &sensor_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  LOG_INFO("TEST: wait for ast init");
  IBEX_SPIN_FOR(sensor_ctrl_ast_init_done(&sensor_ctrl), 1000);
  LOG_INFO("TEST: done ast init");

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    // At POR.
    LOG_INFO("Run clock measurements right after POR");
    CHECK_STATUS_OK(
        clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
            &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
            /*low_speed=*/false));
    busy_spin_micros(delay_micros);

    // check results
    CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
    CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));

    // Set wakeup timer to 100 us to have enough down time, and also wait before
    // entering deep sleep to have a chance to measure before sleeping.
    // As a side-effect of deep sleep the clock measurements are disabled, but
    // recoverable errors are not cleared.
    //
    // Set the counters so we should get an error unless they are cleared.
    uint32_t wakeup_threshold = kDeviceType == kDeviceSimVerilator ? 1000 : 100;
    CHECK_STATUS_OK(
        aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold));

    LOG_INFO("Start clock measurements to cause an error for main and io clk.");
    CHECK_STATUS_OK(
        clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
            &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/true,
            /*low_speed=*/true));
    // Disable writes to measure ctrl registers.
    CHECK_DIF_OK(dif_clkmgr_measure_ctrl_disable(&clkmgr));

    busy_spin_micros(delay_micros);

    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceFive,
        kDifPwrmgrDomainOptionUsbClockInActivePower));

    LOG_INFO("TEST: Issue WFI to enter deep sleep");
    wait_for_interrupt();

  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) == true) {
    // Fail if some measurements are enabled.
    bool all_disabled = UNWRAP(clkmgr_testutils_check_measurement_enables(
        &clkmgr, kDifToggleDisabled));
    CHECK(all_disabled);
    // Check measurement control regwen is enabled.
    dif_toggle_t state;
    CHECK_DIF_OK(dif_clkmgr_measure_ctrl_get_enable(&clkmgr, &state));
    CHECK(state == kDifToggleEnabled);
    LOG_INFO("Check for all clock measurements disabled done");

    // Check we have a measurement error for the main clock.
    dif_clkmgr_recov_err_codes_t expected_err_codes =
        kDifClkmgrRecovErrTypeMainMeas | kDifClkmgrRecovErrTypeIoMeas;
    dif_clkmgr_recov_err_codes_t err_codes;
    CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
    CHECK(err_codes == expected_err_codes,
          "expected main and io clk measurement error 0x%x, but got 0x%x",
          expected_err_codes, err_codes);

    // Clear measurement errors.
    CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr, UINT32_MAX));

    LOG_INFO("TEST: one more measurement");
    CHECK_STATUS_OK(
        clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
            &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
            /*low_speed=*/false));
    busy_spin_micros(delay_micros);
    CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
    CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));

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
