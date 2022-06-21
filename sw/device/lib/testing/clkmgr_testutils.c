// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/clkmgr_testutils.h"

#include "sw/device/lib/dif/dif_clkmgr.h"

static const char *measure_clock_names[kDifClkmgrMeasureClockUsb + 1] = {
    "io_clk", "io_div2_clk", "io_div4_clk", "main_clk", "usb_clk"};

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern bool clkmgr_testutils_get_trans_clock_status(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock);

extern void clkmgr_testutils_check_trans_clock_gating(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    bool exp_clock_enabled, uint32_t timeout_usec);

// The thresholds are encoded as
// - max = count + variability
// - min = count - variability
typedef struct expected_count_info {
  uint32_t count;
  uint32_t variability;
} expected_count_info_t;

// The expected counts are derived from the ratios of the frequencies of the
// various clocks to the AON clock. For example, 48 Mhz / 200 kHz = 240, so
// we set count to 479 and variability to 1, meaning the max threshold is 480,
// and the min to 478. Notice the target counts could be computed from the
// device frequencies, but they are expressed as uint64_t, and are not
// compile-time constants.
static const expected_count_info_t kNoJitterCountInfos[] = {
    {.count = 479, .variability = 1}, {.count = 239, .variability = 1},
    {.count = 119, .variability = 1}, {.count = 499, .variability = 1},
    {.count = 239, .variability = 1},
};

// If jitter is enabled the low threshold should be up to 20% lower, so
// the variability is set to 0.1 * max_count, and count as max - 0.1 * max.
static const expected_count_info_t kJitterCountInfos[] = {
    {.count = 480 - 48, .variability = 48},
    {.count = 240 - 24, .variability = 24},
    {.count = 120 - 12, .variability = 12},
    {.count = 500 - 50, .variability = 50},
    {.count = 240 - 24, .variability = 24},
};

void clkmgr_testutils_enable_clock_count(const dif_clkmgr_t *clkmgr,
                                         dif_clkmgr_measure_clock_t clock,
                                         uint32_t lo_threshold,
                                         uint32_t hi_threshold) {
  LOG_INFO("Enabling clock count measurement for %s(%d) lo %0d hi %0d",
           measure_clock_names[clock], clock, lo_threshold, hi_threshold);
  CHECK_DIF_OK(dif_clkmgr_enable_measure_counts(clkmgr, clock, lo_threshold,
                                                hi_threshold));
}

void clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
    const dif_clkmgr_t *clkmgr, bool jitter_enabled, bool external_clk,
    bool low_speed) {
  CHECK(!(external_clk && jitter_enabled));
  for (int clk = 0; clk < ARRAYSIZE(kNoJitterCountInfos); ++clk) {
    const expected_count_info_t *count_info;
    if (jitter_enabled) {
      count_info = &kJitterCountInfos[clk];
    } else if (external_clk) {
      if (low_speed) {
        if (clk == kDifClkmgrMeasureClockIo ||
            clk == kDifClkmgrMeasureClockMain) {
          count_info = &kNoJitterCountInfos[kDifClkmgrMeasureClockIoDiv2];
        } else {
          count_info = &kNoJitterCountInfos[clk];
        }
      } else {
        if (clk == kDifClkmgrMeasureClockMain) {
          count_info = &kNoJitterCountInfos[kDifClkmgrMeasureClockIo];
        } else {
          count_info = &kNoJitterCountInfos[clk];
        }
      }
    } else {
      count_info = &kNoJitterCountInfos[clk];
    }
    clkmgr_testutils_enable_clock_count(
        clkmgr, (dif_clkmgr_measure_clock_t)clk,
        count_info->count - count_info->variability,
        count_info->count + count_info->variability);
  }
}

void clkmgr_testutils_disable_clock_counts(const dif_clkmgr_t *clkmgr) {
  LOG_INFO("Disabling all clock count measurements");
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    CHECK_DIF_OK(dif_clkmgr_disable_measure_counts(clkmgr, clock));
  }
}

void clkmgr_testutils_check_measurement_counts(const dif_clkmgr_t *clkmgr) {
  dif_clkmgr_recov_err_codes_t err_codes;
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(clkmgr, &err_codes));
  if (err_codes != 0) {
    LOG_ERROR("Unexpected recoverable error codes 0x%x", err_codes);
  } else {
    LOG_INFO("Clock measurements are okay");
  }
  // clear recoverable errors
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(clkmgr, ~0u));
}
