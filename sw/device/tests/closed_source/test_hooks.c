// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/runtime/log.h"

bool manufacturer_pre_test_hook(void) {
  // LOG_INFO("open_source_pre_test_hook");

  // Perform whatever pre-test setup needs to be done.
  // Return true if successful, false if unsuccessful.
  return true;
}

bool manufacturer_post_test_hook(void) {
  // LOG_INFO("open_source_post_test_hook");

  // Perform whatever post-test teardown needs to be done.
  // Return true if successful, false if unsuccessful.
  return true;
}
