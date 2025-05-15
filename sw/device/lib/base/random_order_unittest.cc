// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/random_order.h"

#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace random_order_unittest {
namespace {

using ::testing::Each;
using ::testing::ElementsAre;

uint32_t current_random_word = 0xdeadbeef;

extern "C" uint32_t random_order_random_word(void) {
  return current_random_word;
}

/**
 * Basic invariant checks on a random order context.
 *
 * @param ctx Context to check.
 * @param len Length of the target iteration sequence.
 */
static void ctx_check(random_order_t *ctx, size_t len) {
  // `step` should always be greater than zero.
  EXPECT_LT(0, ctx->step);
  // `state` should always be strictly less than the max.
  EXPECT_LT(ctx->state, ctx->max);

  // `step` should be less than the length if possible.
  if (len > 1) {
    EXPECT_LT(ctx->step, len);
  }

  // `max` should be greater than the length, strictly if possible.
  EXPECT_LE(len, ctx->max);
  if (len < UINT32_MAX) {
    EXPECT_LT(len, ctx->max);
  }
}

TEST(RandomOrder, InitSmallTest) {
  // Check that values are OK for several small `min_len` values.
  random_order_t ctx;
  for (size_t i = 0; i < 100; i++) {
    random_order_init(&ctx, i);
    ctx_check(&ctx, i);
  }
}

TEST(RandomOrder, InitLargeTest) {
  // Check that values are OK for several large `min_len` values.
  random_order_t ctx;
  for (size_t i = 0; i < 100; i++) {
    uint32_t len = UINT32_MAX - i;
    random_order_init(&ctx, len);
    ctx_check(&ctx, len);
  }
}

TEST(RandomOrder, InitRndZeroTest) {
  // Check that zeroes are handled appropriately.
  size_t len = 10;
  uint32_t tmp = current_random_word;
  current_random_word = 0;
  random_order_t ctx;
  random_order_init(&ctx, len);
  ctx_check(&ctx, len);
  current_random_word = tmp;
}

TEST(RandomOrder, SpecTest) {
  // Ensure that advancing through the random order struct hits all numbers in
  // the target sequence.
  size_t len = 100;
  random_order_t ctx;
  random_order_init(&ctx, len);

  std::vector<bool> hit(len);
  for (size_t i = 0; i < len; i++) {
    hit[i] = false;
  }

  for (size_t i = 0; i < random_order_len(&ctx); i++) {
    uint32_t j = random_order_advance(&ctx);
    hit[j] = true;
  }
  RANDOM_ORDER_HARDENED_CHECK_DONE(ctx);

  EXPECT_THAT(hit, Each(true));
}

}  // namespace
}  // namespace random_order_unittest
