// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/sim_dv/lc_ctrl_transition_impl.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  return execute_lc_ctrl_transition_test(/*use_ext_clk=*/false);
}
