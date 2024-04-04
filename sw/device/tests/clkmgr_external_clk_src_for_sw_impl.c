// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This runs a test with external clock enabled via software for either fast
// or slow speed. It checks the expected frequencies via the clock count
// measurement feature. After the measurements are made, the external clock is
// disabled and the clock counts are measured to confirm the frequencies are
// back to what is expected when the external clock is not enabled.

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 200;
static const int kMeasurementsPerRound = 100;

// For passing into `IBEX_SPIN_FOR`.
static bool did_extclk_settle(const dif_clkmgr_t *clkmgr) {
  bool status;
  CHECK_DIF_OK(dif_clkmgr_external_clock_is_settled(clkmgr, &status));
  return status;
}

void execute_clkmgr_external_clk_src_for_sw_test(bool fast_ext_clk) {
  dif_clkmgr_t clkmgr;
  dif_clkmgr_recov_err_codes_t err_codes;

  uint32_t delay_micros = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_us_from_aon_cycles(
      kMeasurementsPerRound, &delay_micros));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr, UINT32_MAX));
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
  CHECK(err_codes == 0, "Unexpected non-zero clkmgr recoverable error code");

  // Configure external clock:
  // - at low speed (48 MHz) both main and io clocks count are the nominal
  //   IoDiv2's.
  // - at high speed (96 MHz) the main clock count is the nominal Io's.
  LOG_INFO("Selecting external clock and %s speed clocks",
           (fast_ext_clk ? "fast" : "slow"));
  CHECK_DIF_OK(
      dif_clkmgr_external_clock_set_enabled(&clkmgr,
                                            /*is_low_speed=*/!fast_ext_clk));

  // Wait for the external clock to become active.
  IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);
  LOG_INFO("External clock enabled");

  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/true,
      /*low_speed=*/!fast_ext_clk));
  busy_spin_micros(delay_micros);

  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));

  // Disable the external clock and check the frequencies are as expected
  // when driven by the AST oscillators.
  LOG_INFO("Disabling external clock");
  CHECK_DIF_OK(dif_clkmgr_external_clock_set_disabled(&clkmgr));

  // Wait for the external clock to become inactive.
  IBEX_SPIN_FOR(!did_extclk_settle(&clkmgr), kSettleDelayMicros);
  LOG_INFO("External clock disabled");

  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
      /*low_speed=*/!fast_ext_clk));
  busy_spin_micros(delay_micros);
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));
  CHECK_STATUS_OK(clkmgr_testutils_disable_clock_counts(&clkmgr));
}
