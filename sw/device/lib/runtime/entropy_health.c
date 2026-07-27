// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/entropy_health.h"

void entropy_health_rct_init(entropy_health_rct_state_t *state,
                             uint32_t first_symbol) {
  if (state == NULL) {
    return;
  }
  state->current_symbol = first_symbol;
  state->rep_count = 1;
  state->fail_flag = 0;
}

void entropy_health_rct_update(entropy_health_rct_state_t *state,
                               uint32_t new_symbol) {
  if (state == NULL) {
    return;
  }

  // Constant-time match evaluation (1 if match, 0 if different)
  uint32_t diff = state->current_symbol ^ new_symbol;

  // Convert diff to a boolean-like 0 or 1 without branching
  // `!!diff` is 1 if diff != 0, so `1 - !!diff` is 1 if matched.
  uint32_t match = 1 - (!!diff);

  // If match == 1: rep_count = rep_count + 1
  // If match == 0: rep_count = 0 + 1 = 1
  state->rep_count = (state->rep_count * match) + 1;
  state->current_symbol = new_symbol;

  // Latch the failure flag if the threshold is reached.
  // Using bitwise OR prevents the flag from clearing once set.
  state->fail_flag |= (state->rep_count >= ENTROPY_HEALTH_RCT_THRESHOLD);
}

bool entropy_health_rct_has_failed(const entropy_health_rct_state_t *state) {
  if (state == NULL) {
    return true; // fail-safe
  }
  return state->fail_flag != 0;
}
