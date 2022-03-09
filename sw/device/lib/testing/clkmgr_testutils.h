// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_

#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/check.h"

/**
 * Returns the transactional block's clock status.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param params clkmgr hardware instance parameters.
 * @param clock The transactional clock ID.
 * @return The transactional block's clock status.
 */
inline bool clkmgr_testutils_get_trans_clock_status(
    dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock) {
  dif_toggle_t state;
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(clkmgr, clock, &state));
  return state == kDifToggleEnabled;
}

/**
 * Verifies clock gating for transactional clocks.
 *
 * For a transactional block, the clock is gated only if the software enables
 * the clock gating AND the block is idle. This function sets the clock gating
 * hint bit to 0 and spinwaits until the clock value matches the expected. It
 * sets the hint back to 1 afterwards. Inlined due to latency-sensitivity.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param clock The transactional clock ID.
 * @param exp_clock_enabled Expected clock status.
 * @param timeout_usec Timeout in microseconds.
 */
inline void clkmgr_testutils_check_trans_clock_gating(
    dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    bool exp_clock_enabled, uint32_t timeout_usec) {
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, 0x0));

  IBEX_SPIN_FOR(clkmgr_testutils_get_trans_clock_status(clkmgr, clock) ==
                    exp_clock_enabled,
                timeout_usec);

  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, 0x1));
}

extern const char *measure_clock_names[kDifClkmgrMeasureClockUsb + 1];

/**
 * Enables clock measurements.
 *
 * This enables measurements with lo and hi count bounds for a given clock.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param clock The clock to be measured.
 * @param lo_threshold Expected minimum cycle count.
 * @param hi_threshold Expected maximum cycle count.
 */
inline void clkmgr_testutils_enable_clock_count_measurement(
    dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock,
    uint32_t lo_threshold, uint32_t hi_threshold) {
  LOG_INFO("Enabling clock count measurement for %0s lo %0d hi %0d",
           measure_clock_names[clock], lo_threshold, hi_threshold);
  CHECK_DIF_OK(dif_clkmgr_enable_measure_counts(clkmgr, clock, lo_threshold,
                                                hi_threshold));
}

/**
 * Disable all clock measurements.
 *
 * @param clkmgr A clkmgr DIF handle.
 */
void clkmgr_testutils_disable_clock_count_measurements(dif_clkmgr_t *clkmgr);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_
