// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/tests/sim_dv/lc_ctrl_transition_impl.h"

const test_config_t kTestConfig;

bool test_main(void) {
  return execute_lc_ctrl_transition_test(/*use_ext_clk=*/true);
}
