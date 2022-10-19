// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  ibex_timeout_t timeout = ibex_timeout_init(HANG_SECS * 1000000);
  while (!ibex_timeout_check(&timeout)) {
  }
  LOG_INFO("Returning after %d seconds", HANG_SECS);
  return true;
}
