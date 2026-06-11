// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/embedpqc/mldsa_test_utils.h"

#include "sw/device/lib/runtime/log.h"

__attribute__((aligned(16))) uint8_t mldsa_stack[MLDSA_STACK_SIZE];

void paint_stack(void) {
  for (size_t i = 0; i < MLDSA_STACK_SIZE; i++) {
    mldsa_stack[i] = 0xA5;
  }
}

size_t get_max_stack_usage(void) {
  for (size_t i = 0; i < MLDSA_STACK_SIZE; i++) {
    if (mldsa_stack[i] != 0xA5) {
      return MLDSA_STACK_SIZE - i;
    }
  }
  return 0;
}

bool check_arrays_eq_verbose(const uint8_t *got, const uint8_t *expected,
                             size_t len) {
  bool match = true;
  for (size_t i = 0; i < len; ++i) {
    if (got[i] != expected[i]) {
      LOG_INFO("Mismatch at index %u: got 0x%02x, expected 0x%02x",
               (unsigned int)i, got[i], expected[i]);
      match = false;
      break;
    }
  }
  return match;
}
