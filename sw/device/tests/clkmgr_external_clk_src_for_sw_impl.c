// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This runs a test with external clock enabled via software for either fast
// or slow speed. It checks the expected frequencies via the clock count
// measurement feature.

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 35;
static const int kMeasurementDelayMicros = 100;

// For passing into `IBEX_SPIN_FOR`.
static bool did_extclk_settle(const dif_clkmgr_t *clkmgr) {
  bool status;
  CHECK_DIF_OK(dif_clkmgr_external_clock_is_settled(clkmgr, &status));
  return status;
}

void execute_clkmgr_external_clk_src_for_sw_test(bool fast_ext_clk) {
  dif_clkmgr_t clkmgr;
  dif_clkmgr_recov_err_codes_t err_codes;

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr, UINT32_MAX));
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
  LOG_INFO("Recoverable error codes 0x%x", err_codes);

  LOG_INFO("Enabling clock count measurements");
  clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/false,
      /*low_speed=*/false);
  busy_spin_micros(kMeasurementDelayMicros);
  clkmgr_testutils_check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_counts(&clkmgr);

  // Configure external clock:
  // - at low speed (48 MHz) both main and io clocks count are the nominal
  //   IoDiv2's.
  // - at high speed (96 MHz) the main clock count is the nominal Io's.
  LOG_INFO("Selecting external clock and %s speed clocks",
           (fast_ext_clk ? "fast" : "slow"));
  CHECK_DIF_OK(
      dif_clkmgr_external_clock_set_enabled(&clkmgr,
                                            /*is_low_speed=*/!fast_ext_clk));

  // Wait a few AON cycles for glitches from the transition to external
  // clock to settle.
  IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);

  clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, /*external_clk=*/true,
      /*low_speed=*/!fast_ext_clk);
  busy_spin_micros(kMeasurementDelayMicros);
  clkmgr_testutils_check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_counts(&clkmgr);
}
