// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_LC_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_LC_CTRL_TESTUTILS_H_

#include <stdbool.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"

/**
 * Print current life cycle state to the console.
 *
 * Reads the life cycle state register and prints the life cycle state as a
 * human readable string. The function errors out in locked/invalid life
 * cycle states where the CPU should not be executing code.
 */
OT_WARN_UNUSED_RESULT
status_t lc_ctrl_testutils_lc_state_log(const dif_lc_ctrl_state_t *state);

/**
 * Checks whether Lifecycle Controller state has debug functions enabled.
 *
 * There could be implications for tests with debug functions enabled. For
 * example, SRAM code execution is enabled when Lifecycle Controller is
 * in one of these states and OTP_IFETCH is disabled.
 */
OT_WARN_UNUSED_RESULT
status_t lc_ctrl_testutils_debug_func_enabled(const dif_lc_ctrl_t *lc_ctrl,
                                              bool *debug_enabled);

/**
 * Check if Lifecycle Controller count number is expected.
 *
 * This function will read out lc_transition_cnt register and check the value
 * against exp_lc_count value.
 */
OT_WARN_UNUSED_RESULT
status_t lc_ctrl_testutils_check_transition_count(const dif_lc_ctrl_t *lc_ctrl,
                                                  uint8_t exp_lc_count);

/**
 * Check if Lifecycle Controller current state is expected.
 *
 * This function will read out lc_state register and check the value
 * against exp_lc_state value.
 */
OT_WARN_UNUSED_RESULT
status_t lc_ctrl_testutils_check_lc_state(const dif_lc_ctrl_t *lc_ctrl,
                                          dif_lc_ctrl_state_t exp_lc_state);

/**
 * Checks the device life cycle state to determine if it is in operational
 * state.
 *
 * @param lc_ctrl Life cycle controller instance.
 * @return OK_STATUS if the device is in PROD, PROD_END or DEV state; otherwise
 * FAILED_PRECONDITION.
 */
OT_WARN_UNUSED_RESULT
status_t lc_ctrl_testutils_operational_state_check(
    const dif_lc_ctrl_t *lc_ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_LC_CTRL_TESTUTILS_H_
