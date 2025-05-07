// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/ibex.h"

// This implementation starts at a random index between 0 and len and
// traverses over all possible indexes with an increment of 1.
// When the maximum value is reached the index wraps back to 0.

/**
 * Returns the ceiling of log2(val + 1) for any input val.
 *
 * If the input val is 0 or bigger than (UINT32_MAX + 1)/2 this function will
 * return 0.
 *
 * @param[in] val A 32 bit operand for the function.
 */
static uint32_t ceil_log_2(uint32_t val) {
  uint32_t x = val - 1;
  x |= x >> 1;
  x |= x >> 2;
  x |= x >> 4;
  x |= x >> 8;
  x |= x >> 16;
  x++;
  return x;
}

void random_order_init(random_order_t *ctx, size_t len) {
  // Find the maximum value for the state by computing the ceiling of log2(len).
  ctx->max = ceil_log_2(len);
  // Initialize the state with a random value between 0 and the max value.
  ctx->state = ((uint64_t)ibex_rnd_uint32() * (uint64_t)ctx->max) >> 32;
  // Initialize the step size with a random odd number within the rande [0,
  // max).
  ctx->step = ((uint64_t)ibex_rnd_uint32() * (uint64_t)ctx->max) >> 32;
  ctx->step &= UINT32_MAX - 1;
}

size_t random_order_len(const random_order_t *ctx) { return ctx->max; }

size_t random_order_advance(random_order_t *ctx) {
  ctx->state = (ctx->state + ctx->step) % ctx->max;
  return ctx->state;
}
