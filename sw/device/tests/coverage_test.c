// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_coverage.h"
#include "sw/device/lib/testing/test_main.h"

static void spin_45(uint8_t state) {
  static const char kSpinnerChars[] = "|/-\\";
  base_printf("%c\r", kSpinnerChars[state]);
}

static void spin_180(void) {
  for (uint8_t state = 0; state < 4; ++state) {
    spin_45(state);
    usleep(100 * 1000);  // 0.1s
  }
}

const test_config_t kTestConfig;

/**
 * A simple program for testing the coverage functionality.
 *
 * Prints a message and displays a spinning bar.
 */
bool test_main(void) {
  // Print an assuring message.
  LOG_INFO("Collecting coverage data.");
  // Display a spinning bar.
  for (uint8_t i = 0; i < 4; ++i) {
    spin_180();
  }
  return true;
}
