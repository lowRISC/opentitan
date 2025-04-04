// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
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
 * This test measures clock counts with clkmgr frequency measurements and
 * jitter enabled, performing 100 measurements per round, where a round is
 * one AON clock cycle. Measurement errors (fast or slow clocks) are recorded
 * as recoverable errors in clkmgr.
 *
 * This assumes clocks have been calibrated:
 * - for silicon validation this means clocks are calibrated, which means SV1
 *   tasks are completed
 * - for simulation it requires overriding the hardware behavior via plusargs
 *   so it runs with calibrated USB clock, or the USB clock frequency will be
 *   incorrect.
 *
 * When jitter is enabled it checks that using jitter thresholds the checks
 * pass, and with normal thresholds we encounter recoverable errors.
 *
 * When jitter is disabled it checks that neither set of thresholds cause
 * errors.
 *
 * The test flow depends on jitter enable lock:
 * - if it is locked this only tests for the given jitter configuration.
 * - if it is unlocked this tests for both jitter enabled and disabled.
 *
 * FPGA emulation platforms don't support jittery clocks so some of the
 * checks are bypassed for them.
 */
enum {
  kMeasurementsPerRound = 100,
};

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_clkmgr_t kClkmgrDt = 0;
static_assert(kDtClkmgrCount == 1, "this test expects a clkmgr");

static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;

// Test with thresholds for jitter enabled expecting no failures, and then
// with thresholds for jitter disabled expecting failures.
static void test_clock_frequencies_with_jitter_enabled(uint32_t delay_micros) {
  LOG_INFO("Testing frequencies with jitter enabled");
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/true, /*external_clk=*/false,
      /*low_speed=*/false));
  busy_spin_micros(delay_micros);
  // This checks there are no errors.
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));
  if (kDeviceType == kDeviceSimDV || kDeviceType == kDeviceSilicon) {
    // Set thresholds for jitter disabled expecting failures.
    CHECK_STATUS_OK(
        clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
            &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
            /*low_speed=*/false));
    busy_spin_micros(delay_micros);
    dif_clkmgr_recov_err_codes_t err_codes;
    CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
    CHECK(err_codes != 0);
    // Clear errors.
    CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));
    CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr, err_codes));
  } else {
    LOG_INFO("Testing with jitter enabled but no-jitter thresholds %s",
             "is not viable for FPGAs");
  }
}

static void test_clock_frequencies_with_jitter_disabled(uint32_t delay_micros) {
  LOG_INFO("Testing frequencies with jitter disabled");
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
      /*low_speed=*/false));
  busy_spin_micros(delay_micros);
  // This checks there are no errors.
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));
  // Set thresholds for jitter disabled expecting no failures.
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/true, /*external_clk=*/false,
      /*low_speed=*/false));
  busy_spin_micros(delay_micros);
  LOG_INFO("Checking measurement counts");
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
}

bool test_main(void) {
  dif_sensor_ctrl_t sensor_ctrl;

  uint32_t delay_micros = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_us_from_aon_cycles(
      kMeasurementsPerRound, &delay_micros));

  CHECK_DIF_OK(dif_clkmgr_init_from_dt(kClkmgrDt, &clkmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR),
      &sensor_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  LOG_INFO("TEST: wait for ast init");
  IBEX_SPIN_FOR(sensor_ctrl_ast_init_done(&sensor_ctrl), 1000);
  LOG_INFO("TEST: done ast init");

  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true);

  bool jitter_locked;
  CHECK_DIF_OK(dif_clkmgr_jitter_enable_is_locked(&clkmgr, &jitter_locked));
  if (jitter_locked) {
    dif_toggle_t jitter_status;
    CHECK_DIF_OK(dif_clkmgr_jitter_get_enabled(&clkmgr, &jitter_status));
    if (jitter_status == kDifToggleEnabled) {
      test_clock_frequencies_with_jitter_enabled(delay_micros);
    } else {
      test_clock_frequencies_with_jitter_disabled(delay_micros);
    }
  } else {
    CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, kDifToggleEnabled));
    test_clock_frequencies_with_jitter_enabled(delay_micros);
    CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, kDifToggleDisabled));
    test_clock_frequencies_with_jitter_disabled(delay_micros);
  }
  return true;
}
