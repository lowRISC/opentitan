// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/tests/sim_dv/lc_ctrl_transition_impl.h"

bool test_main(void) {
  return execute_lc_ctrl_transition_test(/*use_ext_clk=*/true);
}
