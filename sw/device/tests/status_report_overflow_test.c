// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/status_report_unittest_c.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();
OTTF_OVERRIDE_STATUS_REPORT_LIST(3)

bool test_main(void) {
  // Manually push items on the stack to overflow the list.
  for (size_t i = 0; i < 100; i++)
    status_report(UNKNOWN());
  status_report(DEADLINE_EXCEEDED());
  status_report(CANCELLED());
  status_report(UNAVAILABLE());
  status_report(ABORTED());
  // Make the test fails so it prints the status.
  return false;
}
