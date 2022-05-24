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

typedef struct expected_count_info {
  int count;
  int variability;
} expected_count_info_t;

static const expected_count_info_t kCountInfos[] = {
    {.count = 479, .variability = 1}, {.count = 239, .variability = 1},
    {.count = 119, .variability = 1}, {.count = 499, .variability = 1},
    {.count = 239, .variability = 1},
};

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 35;
static const int kMeasurementDelayMicros = 100;

static void clear_recoverable_errors(const dif_clkmgr_t *clkmgr) {
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(clkmgr, ~0u));
}

static void check_measurement_counts(const dif_clkmgr_t *clkmgr) {
  dif_clkmgr_recov_err_codes_t err_codes;
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(clkmgr, &err_codes));
  if (err_codes != 0) {
    LOG_ERROR("Unexpected recoverable error codes 0x%x", err_codes);
  } else {
    LOG_INFO("Clock measurements are okay");
  }
  clear_recoverable_errors(clkmgr);
}

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
  // Enable cycle count measurements to confirm the frequencies are correct.
  for (size_t i = 0; i < ARRAYSIZE(kCountInfos); ++i) {
    expected_count_info_t count_info = kCountInfos[i];
    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, (dif_clkmgr_measure_clock_t)i,
        count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  busy_spin_micros(kMeasurementDelayMicros);
  check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);

  // Configure external clock:
  // - at low speed (48 MHz) both main and io clocks count are the nominal
  //   IoDiv2's.
  // - at high speed (96 MHz) the main clock count is the nominal Io's.
  LOG_INFO("Selecting external clock and low speed clocks");
  CHECK_DIF_OK(
      dif_clkmgr_external_clock_set_enabled(&clkmgr,
                                            /*is_low_speed=*/!fast_ext_clk));

  // Wait a few AON cycles for glitches from the transition to external
  // clock to settle.
  IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);

  // Enable cycle measurements to confirm the frequencies are correct.
  for (size_t i = 0; i < ARRAYSIZE(kCountInfos); ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;

    expected_count_info_t count_info = kCountInfos[i];
    if (fast_ext_clk && clock == kDifClkmgrMeasureClockMain) {
      count_info = kCountInfos[kDifClkmgrMeasureClockIo];
    } else if (!fast_ext_clk && (clock == kDifClkmgrMeasureClockIo ||
                                 clock == kDifClkmgrMeasureClockMain)) {
      count_info = kCountInfos[kDifClkmgrMeasureClockIoDiv2];
    }

    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, clock, count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  busy_spin_micros(kMeasurementDelayMicros);
  check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);
}
