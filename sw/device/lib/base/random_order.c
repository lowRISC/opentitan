// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"

void random_order_init(random_order_t *ctx, size_t min_len) {
  ctx->ctr = 0;
  if (min_len > 0) {
    ctx->state = random_order_random_word() % min_len;
  } else {
    ctx->state = 0;
  }
  ctx->max = min_len;
}

size_t random_order_len(const random_order_t *ctx) { return ctx->max; }

size_t random_order_advance(random_order_t *ctx) {
  size_t out = ctx->state;
  // Compute the next value and next value if we overflow max.
  size_t next = ctx->state + 1;
  size_t next_overflow = next - ctx->max;

  // Is next strictly less than max?
  ct_bool32_t which = ct_sltu32(next, ctx->max);
  // If yes, choose next, else next_overflow.
  ctx->state = ct_cmov32(which, next, next_overflow);

  ctx->ctr = launder32(ctx->ctr) + 1;
  HARDENED_CHECK_LE(ctx->state, ctx->max);
  return out;
}
