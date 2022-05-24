// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CLKMGR_EXTERNAL_CLK_SRC_FOR_SW_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_CLKMGR_EXTERNAL_CLK_SRC_FOR_SW_IMPL_H_

#include <stdbool.h>

/**
 * This test enables the external clock running at high or low speed.
 * It checks the expected frequencies via the clock count measurement feature.
 *
 * @param fast_ext_clk When true, run the test for an external clock running
 *                     at 96 MHz.
 */
void execute_clkmgr_external_clk_src_for_sw_test(bool fast_ext_clk);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CLKMGR_EXTERNAL_CLK_SRC_FOR_SW_IMPL_H_
