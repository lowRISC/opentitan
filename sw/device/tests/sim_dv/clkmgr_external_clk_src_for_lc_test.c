// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/sim_dv/lc_ctrl_transition_impl.h"

OTTF_DEFINE_TEST_CONFIG();

// Track the value of the external clock enable CSR written by software.
static volatile const uint8_t kExternalClockEnable = 0x1;

bool test_main(void) {
  return execute_lc_ctrl_transition_test(/*use_ext_clk=*/kExternalClockEnable);
}
