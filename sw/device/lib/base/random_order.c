// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"

// The source of randomness for init(), which may be replaced at link-time.
OT_WEAK
uint32_t random_order_random_word(void) { return 0xcaffe17f; }

void random_order_init(random_order_t *ctx, size_t min_len) {
  if (min_len == 0) {
    ctx->index = 0;
    ctx->max = 0;
  }

  ctx->state = random_order_random_word();
  ctx->index = 0;
  ctx->max = bitfield_next_power_of_two32(min_len + 1);
}

size_t random_order_len(const random_order_t *ctx) { return ctx->max; }

size_t random_order_advance(random_order_t *ctx) {
  // This function implements "quadratic probing", a technique used by modern
  // open-addressing hash tables for using hash entropy to scatter elements in
  // the table in a way that tends to avoid clustering.
  //
  // This algorithm is also useful for converting the initial randomness from
  // init() into a random-looking traversal of the region to be copied. This
  // specific formula is triangular probing:
  //
  // f(n) := entropy + (n^2 - n)/2
  //
  // This is easy to compute step-by-step, and is guaranteed to visit every slot
  // of a power-of-two array exactly once; init() ensures that we're pretending
  // the maximum size is, in fact, a power of two.
  //
  // See https://en.wikipedia.org/wiki/Quadratic_probing.

  // This must be postincrement so that the last value of `index` we add to
  // `state` is `max - 1`; if we did not do this, the final value would be
  // `max`, which the mask below would undo. This causes the final index to
  // be repeated and, as a result, potentially causes another index
  // somewhere to get skipped.
  ctx->state += ctx->index++;
  return ctx->state & (ctx->max - 1);
}
