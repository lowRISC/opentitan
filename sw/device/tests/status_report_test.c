// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/status_report_unittest_c.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t status = status_report_unittest_c();
  // push the returned status for easier checking
  status_report(status);
  // make the test fails so it prints the status
  return false;
}
