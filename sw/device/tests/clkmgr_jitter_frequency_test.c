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
 */
enum {
  kMeasurementsPerRound = 100,
};

static dif_clkmgr_t clkmgr;
static dif_pwrmgr_t pwrmgr;

bool test_main(void) {
  dif_sensor_ctrl_t sensor_ctrl;

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

  LOG_INFO("TEST: wait for ast init");
  IBEX_SPIN_FOR(sensor_ctrl_ast_init_done(&sensor_ctrl), 1000);
  LOG_INFO("TEST: done ast init");

  CHECK(UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true);

  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/true, /*external_clk=*/false,
      /*low_speed=*/false));
  busy_spin_micros(delay_micros);

  // check results
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));

  return true;
}
