// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Initialize OTTF.
OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Invalidate instruction cache.
  icache_invalidate();

  return true;
}
