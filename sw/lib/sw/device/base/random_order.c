// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include "sw/device/lib/base/bitfield.h"

// TODO: The current implementation is just a skeleton, and currently just
// traverses from 0 to `min_len * 2`.

void random_order_init(random_order_t *ctx, size_t min_len) {
  ctx->state = 0;
  ctx->max = min_len * 2;
}

size_t random_order_len(const random_order_t *ctx) { return ctx->max; }

size_t random_order_advance(random_order_t *ctx) { return ctx->state++; }
