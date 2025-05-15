// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"

void random_order_init(random_order_t *ctx, size_t min_len) {
  ctx->ctr = 0;

  // If the sequence length is zero or one, there's not much randomization we
  // can do, but we can at least return one value past the range.
  if (launder32(min_len) < 2) {
    ctx->state = 0;
    ctx->step = 1;
    ctx->max = min_len + 1;
    return;
  }
  HARDENED_CHECK_LE(2, min_len);

  // Sample the start index from the range [0, n-1].
  ctx->state = random_order_random_word() % min_len;
  // Sample the step size from the range [1, n-1].
  ctx->step = (random_order_random_word() % (min_len - 1)) + 1;

  if (min_len - (min_len % ctx->step) > UINT32_MAX - ctx->step) {
    // Safe fallback for cases where the max calculation would overflow.
    ctx->max = UINT32_MAX;
    ctx->step = 1;
  } else {
    // The maximum value is the smallest multiple of `step` that is strictly
    // greater than `min_len`.
    ctx->max = min_len - (min_len % ctx->step) + ctx->step;
  }
  HARDENED_CHECK_LE(min_len, ctx->max);
}

size_t random_order_len(const random_order_t *ctx) { return ctx->max; }

size_t random_order_advance(random_order_t *ctx) {
  size_t out = ctx->state;

  // Normally, the increment is the step size. However, if we came back around
  // to the start index, increase it by one to change the offset of the step.
  uint32_t inc = ctx->step;
  ctx->ctr = launder32(ctx->ctr) + 1;
  if (ctx->ctr % (ctx->max / ctx->step) == 0) {
    inc++;
  }

  if (launder32(inc) >= ctx->max - ctx->state) {
    // If the next step would be greater than the maximum value, then loop back
    // around to the start.
    ctx->state = ctx->state + inc - ctx->max;
  } else {
    ctx->state += inc;
  }
  HARDENED_CHECK_LE(ctx->state, ctx->max);

  return out;
}
