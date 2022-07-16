// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_

#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

/**
 * Returns the transactional block's clock status.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param params clkmgr hardware instance parameters.
 * @param clock The transactional clock ID.
 * @return The transactional block's clock status.
 */
inline bool clkmgr_testutils_get_trans_clock_status(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock) {
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
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    bool exp_clock_enabled, uint32_t timeout_usec) {
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, 0x0));

  IBEX_SPIN_FOR(clkmgr_testutils_get_trans_clock_status(clkmgr, clock) ==
                    exp_clock_enabled,
                timeout_usec);

  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, 0x1));
}

/**
 * Returns the name of a measured clock.
 */
const char *clkmgr_testutils_measurement_name(dif_clkmgr_measure_clock_t clock);

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
void clkmgr_testutils_enable_clock_count(const dif_clkmgr_t *clkmgr,
                                         dif_clkmgr_measure_clock_t clock,
                                         uint32_t lo_threshold,
                                         uint32_t hi_threshold);

/**
 * Enables all clock measurements with expected thresholds.
 *
 * If jitter is disabled the thresholds are configured tightly.
 * If jitter is enabled the min threshold allows more variability.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param jitter_enabled If true relax the min threshold.
 * @param external_clk If true the external clock is enabled.
 * @param low_speed If true and external clock is enabled, the external
 *                  clock is running at 48 Mhz.
 */
void clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
    const dif_clkmgr_t *clkmgr, bool jitter_enabled, bool external_clk,
    bool low_speed);

/**
 * Checks that there are no clock measurement errors.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @return False if any measurement has errors.
 */
OT_WARN_UNUSED_RESULT
bool clkmgr_testutils_check_measurement_counts(const dif_clkmgr_t *clkmgr);

/**
 * Check all measurement enables.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param expected_status The expected status of the enables.
 * @return False if any enable status is unexpected.
 */
OT_WARN_UNUSED_RESULT
bool clkmgr_testutils_check_measurement_enables(const dif_clkmgr_t *clkmgr,
                                                dif_toggle_t expected_status);

/**
 * Disable all clock measurements.
 *
 * @param clkmgr A clkmgr DIF handle.
 */
void clkmgr_testutils_disable_clock_counts(const dif_clkmgr_t *clkmgr);

/**
 * Switch to use external clock and wait until the switching is done
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param is_low_speed Is external clock in low speed mode or not.
 */
void clkmgr_testutils_enable_external_clock_and_wait_for_completion(
    const dif_clkmgr_t *clkmgr, bool is_low_speed);

/**
 * Verifies the given clock state.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param clock_id The transactional clock ID.
 * @param expected_state Expected clock state.
 */
#define CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, clock_id, expected_state) \
  do {                                                                      \
    dif_toggle_t clock_state;                                               \
    CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(&clkmgr, clock_id,   \
                                                       &clock_state));      \
    CHECK(clock_state == expected_state,                                    \
          "Clock enabled state is (%d) and not as expected (%d).",          \
          clock_state, expected_state);                                     \
  } while (0)

/**
 * Set and verifies the given clock state.
 *
 * @param clkmgr A clkmgr DIF handle.
 * @param clock_id The transactional clock ID.
 * @param new_state Clock state to be set.
 * @param expected_state Expected clock state.
 */
#define CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(clkmgr, clock_id, new_state, \
                                                  expected_state)              \
  do {                                                                         \
    CHECK_DIF_OK(                                                              \
        dif_clkmgr_hintable_clock_set_hint(&clkmgr, clock_id, new_state));     \
    CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, clock_id, expected_state);       \
  } while (0)

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_
