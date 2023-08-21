// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
#ifdef EMPTY_TEST_MSG
  LOG_INFO(EMPTY_TEST_MSG);
#endif
  // Wait in a loop so that OpenOCD can connect to the TAP without the ROM
  // resetting the chip.
  while (1) {
  }
  return true;
}
