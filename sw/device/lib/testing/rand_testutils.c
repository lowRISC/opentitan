// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rand_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"

/**
 * The polynomial co-efficients used in the 32-bit LFSR implementation.
 *
 * This implementation matches the RTL design at `hw/ip/prim/rtl/prim_lfsr.sv`.
 */
const uint32_t kLfsrCoefficients = 0x80000057;

uint32_t rand_testutils_gen32(void) {
  static uint32_t lfsr = 1;
  bool lsb = lfsr & 0x1u;
  lfsr >>= 1;
  if (lsb) {
    lfsr ^= kLfsrCoefficients;
  }
  return lfsr;
}

uint32_t rand_testutils_gen32_range(uint32_t min, uint32_t max) {
  CHECK(max >= min);
  uint32_t range = max - min;
  if (range == 0) {
    return min;
  }
  return min + (rand_testutils_gen32() % (range + 1));
}
