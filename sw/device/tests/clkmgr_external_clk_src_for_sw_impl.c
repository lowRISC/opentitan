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
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

typedef struct expected_count_info {
  int count;
  int variability;
} expected_count_info_t;

expected_count_info_t count_infos[kDifClkmgrMeasureClockUsb + 1] = {
    {479, 1}, {239, 1}, {119, 1}, {499, 1}, {239, 1}};

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
const int extclk_settle_delay_us = 35;
const int measurement_delay_us = 100;

static void clear_recoverable_errors(const dif_clkmgr_t *clkmgr) {
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(clkmgr, ~0u));
}

static void check_measurement_counts(const dif_clkmgr_t *clkmgr) {
  dif_clkmgr_recov_err_codes_t err_codes;
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(clkmgr, &err_codes));
  if (err_codes) {
    LOG_ERROR("Unexpected recoverable error codes 0x%x", err_codes);
  } else {
    LOG_INFO("Clock measurements are okay");
  }
  clear_recoverable_errors(clkmgr);
}

static bool did_extclk_settle(const dif_clkmgr_t *clkmgr) {
  bool status;
  CHECK_DIF_OK(dif_clkmgr_external_clock_is_settled(clkmgr, &status));
  return status;
}

bool execute_clkmgr_external_clk_src_for_sw_test(bool fast_ext_clk) {
  dif_clkmgr_t clkmgr;
  dif_clkmgr_recov_err_codes_t err_codes;

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr, ~0u));
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(&clkmgr, &err_codes));
  LOG_INFO("Recoverable error codes 0x%x", err_codes);

  LOG_INFO("Enabling clock count measurements");
  // Enable cycle count measurements to confirm the frequencies are correct.
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    expected_count_info_t count_info = count_infos[clock];
    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, clock, count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  busy_spin_micros(measurement_delay_us);
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
  IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), extclk_settle_delay_us);

  // Enable cycle measurements to confirm the frequencies are correct.
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    expected_count_info_t count_info;
    if (fast_ext_clk) {
      if (clock == kDifClkmgrMeasureClockMain) {
        count_info = count_infos[kDifClkmgrMeasureClockIo];
      } else {
        count_info = count_infos[clock];
      }
    } else {
      if (clock == kDifClkmgrMeasureClockIo ||
          clock == kDifClkmgrMeasureClockMain) {
        count_info = count_infos[kDifClkmgrMeasureClockIoDiv2];
      } else {
        count_info = count_infos[clock];
      }
    }
    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, clock, count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  busy_spin_micros(measurement_delay_us);
  check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);

  return true;
}
