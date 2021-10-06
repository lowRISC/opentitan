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
    dif_clkmgr_t *clkmgr, dif_clkmgr_params_t params,
    dif_clkmgr_hintable_clock_t clock) {
  bool clock_enabled;
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(clkmgr, params, clock,
                                                     &clock_enabled));
  return clock_enabled;
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
 * @param params clkmgr hardware instance parameters.
 * @param clock The transactional clock ID.
 * @param exp_clock_enabled Expected clock status.
 * @param timeout_usec Timeout in microseconds.
 */
inline void clkmgr_testutils_check_trans_clock_gating(
    dif_clkmgr_t *clkmgr, dif_clkmgr_params_t params,
    dif_clkmgr_hintable_clock_t clock, bool exp_clock_enabled,
    uint32_t timeout_usec) {
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(clkmgr, params, clock, 0x0));

  IBEX_SPIN_FOR(clkmgr_testutils_get_trans_clock_status(
                    clkmgr, params, clock) == exp_clock_enabled,
                timeout_usec);

  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(clkmgr, params, clock, 0x1));
}

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_CLKMGR_TESTUTILS_H_
