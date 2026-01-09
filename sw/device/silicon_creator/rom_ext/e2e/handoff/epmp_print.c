// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dbg_print_epmp();
  return true;
}
