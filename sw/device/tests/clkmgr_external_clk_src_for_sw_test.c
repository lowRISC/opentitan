// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This test enables the external clock via software and ramps down the
// clock dividers. It checks the expected frequencies via the clock count
// measurement feature.
//
// The variability for USB is larger because that clock is uncalibrated at
// power-on. We can tighten up the USB measurement once
// https://github.com/lowRISC/opentitan/issues/11264 is addressed.

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

typedef struct expected_count_info {
  int count;
  int variability;
} expected_count_info_t;

expected_count_info_t count_infos[kDifClkmgrMeasureClockUsb + 1] = {
  {479, 1}, {239, 1}, {119, 1}, {479, 1}, {239, 6}};

const int measurement_delay_us = 50;

static void sleep_us(int delay_us) {
  ibex_timeout_t timeout = ibex_timeout_init(delay_us);
  while (true) {
    if (ibex_timeout_check(&timeout))
      break;
  }
}

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

  //sleep_us(measurement_delay_us);
  //check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);

  // Configure external clock to high speed
  // When external clock is high speed, main / io clocks are close to nominal speeds and
  // io_div2/io_div4/usb are at expected frequencies.
  LOG_INFO("Selecting high speed external clock. Internal clocks should have nominal speeds");
  CHECK_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr, false));

  // Wait a few AON cycles for glitches from the transition to external
  // clock to settle.
  sleep_us(measurement_delay_us);
  check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);

  // Configure external clock to low speed
  // When external clock is low speed, main / io are at half frequency.
  // io_div2/io_div4/usb are at expected frequencies
  LOG_INFO("Selecting low speed external clock.");
  CHECK_DIF_OK(dif_clkmgr_external_clock_set_enabled(&clkmgr, true));

  // Wait a few AON cycles for glitches from the transition to external
  // high speed to settle.
  sleep_us(50);

  // Enable cycle measurements to confirm the frequencies are correct.
  // In this test, even though we configured low speed, the external clock is still high speed.
  // This gets in a weird situation where all clocks other than io/main are sped up.
  // So this means relative to everything else, Main/IO now look "slower", while everything else
  // is the "same" speed.
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    expected_count_info_t count_info;
    if (clock == kDifClkmgrMeasureClockMain ||
	clock == kDifClkmgrMeasureClockIo) {
      count_info = count_infos[kDifClkmgrMeasureClockIoDiv2];
    } else {
      count_info = count_infos[clock];
    }
    clkmgr_testutils_enable_clock_count_measurement(
        &clkmgr, clock, count_info.count - count_info.variability,
        count_info.count + count_info.variability);
  }

  sleep_us(measurement_delay_us);
  check_measurement_counts(&clkmgr);
  clkmgr_testutils_disable_clock_count_measurements(&clkmgr);

  return true;
}
