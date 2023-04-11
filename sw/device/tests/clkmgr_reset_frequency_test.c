// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sensor_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * This test measure clock counts with clkmgr frequency measurements, performing
 * 100 measurements per round. Measurement errors (fast or slow clocks) are
 * recorded as recoverable error in clkmgr.
 *
 * This test configures the clock thresholds so it generates errors, after 100
 * measurements it checks that some errors are found, then a reset is triggered,
 * and it checks the measurements should be disabled, and no errors should be
 * reported.
 *
 * Notice the test overrides the hardware behavior so it comes out with
 * calibrated USB clock, otherwise the USB clock frequency will be incorrect.
 * USB calibration should be a separate test, and may be vendor-specific.
 */
enum {
  kWaitForCSRPolling = 1,  // 1us
  kMeasurementsPerRound = 100,
};

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  dif_rstmgr_t rstmgr;
  dif_sensor_ctrl_t sensor_ctrl;

  uint32_t delay_micros = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_us_from_aon_cycles(
      kMeasurementsPerRound, &delay_micros));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR),
      &sensor_ctrl));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  LOG_INFO("TEST: wait for ast init");
  IBEX_SPIN_FOR(sensor_ctrl_ast_init_done(&sensor_ctrl), 1000);
  LOG_INFO("TEST: done ast init");

  if (UNWRAP(
          rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoPor))) {
    LOG_INFO("POR reset");

    // Configure the counters to trigger an error by setting them for external
    // clocks.
    CHECK_STATUS_OK(
        clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
            &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/true,
            /*low_speed=*/true));
    busy_spin_micros(delay_micros);

    // Check we get errors, but let the counters keep going.
    dif_clkmgr_recov_err_codes_t err_codes;
    CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
    CHECK(err_codes != 0);

    // Trigger a rstmgr SW reset.
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  } else if (UNWRAP(rstmgr_testutils_reset_info_any(&rstmgr,
                                                    kDifRstmgrResetInfoSw))) {
    LOG_INFO("Back from rstmgr SW reset");
    bool all_disabled = UNWRAP(clkmgr_testutils_check_measurement_enables(
        &clkmgr, kDifToggleDisabled));
    CHECK(all_disabled);

    CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
    return true;
  } else {
    dif_rstmgr_reset_info_bitfield_t rst_info;
    CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &rst_info));
    LOG_ERROR("Unexpected rst_info 0x%x", rst_info);
    return false;
  }
  return true;
}
