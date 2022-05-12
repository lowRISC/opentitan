// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_LC_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_LC_CTRL_TESTUTILS_H_

#include <stdbool.h>

#include "sw/device/lib/dif/dif_lc_ctrl.h"

/**
 * Checks whether Lifecycle Controller state has debug functions enabled.
 *
 * There could be implications for tests with debug functions enabled. For
 * example, SRAM code execution is enabled when Lifecycle Controller is
 * in one of these states and OTP_IFETCH is disabled.
 */
bool lc_ctrl_testutils_debug_func_enabled(const dif_lc_ctrl_t *lc_ctrl);

/**
 * Check if Lifecycle Controller count number is expected.
 *
 * This function will read out lc_transition_cnt register and check the value
 * against exp_lc_count value.
 */
void lc_ctrl_testutils_check_transition_count(const dif_lc_ctrl_t *lc_ctrl,
                                              uint8_t exp_lc_count);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_LC_CTRL_TESTUTILS_H_
