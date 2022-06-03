// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/runtime/log.h"

bool manufacturer_pre_test_hook(void) {
  LOG_INFO("Manufacturer pre-test hook running ...");

  // Perform whatever pre-test setup needs to be done.
  // Return true if successful, false if unsuccessful.
  return true;
}

bool manufacturer_post_test_hook(void) {
  LOG_INFO("Manufacturer post-test hook running ...");

  // Perform whatever post-test teardown needs to be done.
  // Return true if successful, false if unsuccessful.
  return true;
}
