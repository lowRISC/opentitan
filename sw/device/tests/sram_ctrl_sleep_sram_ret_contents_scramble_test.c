// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sram_ctrl_sleep_sram_ret_contents_impl.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  return execute_sram_ctrl_sleep_ret_sram_contents_test(true);
}
