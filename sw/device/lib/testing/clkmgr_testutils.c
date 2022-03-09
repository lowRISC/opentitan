// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/clkmgr_testutils.h"

#include "sw/device/lib/dif/dif_clkmgr.h"

const char *measure_clock_names[kDifClkmgrMeasureClockUsb + 1] = {
    "io_clk", "io_div2_clk", "io_div4_clk", "main_clk", "usb_clk"};

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern bool clkmgr_testutils_get_trans_clock_status(
    dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock);

extern void clkmgr_testutils_check_trans_clock_gating(
    dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    bool exp_clock_enabled, uint32_t timeout_usec);

extern void clkmgr_testutils_enable_clock_count_measurement(
    dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock,
    uint32_t lo_threshold, uint32_t hi_threshold);

void clkmgr_testutils_disable_clock_count_measurements(dif_clkmgr_t *clkmgr) {
  LOG_INFO("Disabling all clock count measurements");
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    CHECK_DIF_OK(dif_clkmgr_disable_measure_counts(clkmgr, clock));
  }
}
