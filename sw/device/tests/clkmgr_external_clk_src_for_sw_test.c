// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This test enables the external clock via software and ramps down the
// clock dividers. It checks the expected frequencies via the clock count
// measurement feature.
//
// The variability for USB is larger because that clock is uncalibrated at
// power-on.
// TODO(lowrisc/opentitan:#11264): tighten up the USB measurement once
// this issue is addressed.

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
    {479, 1}, {239, 1}, {119, 1}, {499, 1}, {239, 6}};

const int extclk_settle_delay_us = 30;
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

bool test_main() {
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

  // Configure external clock and low speed: both main and io clocks counts
  // are the nominal IoDiv2's.
  LOG_INFO("Selecting external clock and low speed clocks");
  CHECK_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr, true));

  // Wait a few AON cycles for glitches from the transition to external
  // clock to settle.
  busy_spin_micros(extclk_settle_delay_us);

  // Enable cycle measurements to confirm the frequencies are correct.
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    expected_count_info_t count_info;
    if (clock == kDifClkmgrMeasureClockIo ||
        clock == kDifClkmgrMeasureClockMain) {
      count_info = count_infos[kDifClkmgrMeasureClockIoDiv2];
    } else {
      count_info = count_infos[clock];
    }
    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, clock, count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  busy_spin_micros(measurement_delay_us);
  check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);

  // Configure external clock and high speed: io, io_div2, and main expected
  // at 96 MHz, and io_div4 at 48 MHz.
  LOG_INFO("Selecting external clock and high speed clocks");
  CHECK_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr, false));

  // Wait a few AON cycles for glitches from the transition to external
  // high speed to settle.
  busy_spin_micros(10);

  // Enable cycle measurements to confirm the frequencies are correct.
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    expected_count_info_t count_info;
    if (clock == kDifClkmgrMeasureClockMain ||
        clock == kDifClkmgrMeasureClockIoDiv2) {
      count_info = count_infos[kDifClkmgrMeasureClockIo];
    } else if (clock == kDifClkmgrMeasureClockIoDiv4) {
      count_info = count_infos[kDifClkmgrMeasureClockIoDiv2];
    } else {
      count_info = count_infos[clock];
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
