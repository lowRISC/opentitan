// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/crypto/drivers/ibex.h"

// This implementation starts at a random index between 0 and len and
// traverses over all possible indexes with an increment of 1.
// When the maximum value is reached the index wraps back to 0.

void random_order_init(random_order_t *ctx, size_t len) {
  ctx->state = ((uint64_t)ibex_rnd_uint32() * (uint64_t)len) >> 32;
  ctx->max = len;
}

size_t random_order_len(const random_order_t *ctx) { return ctx->max; }

size_t random_order_advance(random_order_t *ctx) {
  ctx->state = (ctx->state + 1) % ctx->max;
  return ctx->state;
}
