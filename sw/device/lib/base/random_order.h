// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_RANDOM_ORDER_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_RANDOM_ORDER_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief Functions for generating random traversal orders.
 */

/**
 * Expects some external implementation of randomness to be linked.
 *
 * @return A fresh random word.
 */
extern uint32_t random_order_random_word(void);

/**
 * Context for a random traversal order.
 *
 * A "random traversal order" specifies a random order to walk through some
 * buffer of length `n`, which is an important building block for
 * constant-power code. Given `n`, the random order emits integers in the
 * range `0..m`, where `m` is an implementation-defined, per-random-order
 * value greater than `n`. The order is guaranteed to visit each integer in
 * `0..n` at least once, but with some caveats:
 * - Values greater than `n` may be returned.
 * - The same value may be returned multiple times.
 *
 * Users must be mindful of these constraints when using `random_order_t`.
 * These caveats are intended to allow for implementation flexibility, such as
 * intentionally adding decoys to the sequence.
 */
typedef struct random_order {
  /**
   * Next index to return.
   */
  size_t state;
  /**
   * Step size.
   */
  size_t step;
  /**
   * Maximum index to return (exclusive).
   */
  size_t max;
  /**
   * Total number of iterations so far.
   */
  size_t ctr;
} random_order_t;

/**
 * Hardened check that a random_order iteration is complete.
 *
 * @param ctx The context to check.
 */
#define RANDOM_ORDER_HARDENED_CHECK_DONE(ctx_) \
  HARDENED_CHECK_EQ(ctx_.max, ctx_.ctr)

/**
 * Constructs a new, randomly-seeded traversal order,
 * running from `0` to at least `min_len`.
 *
 * This function does not take a seed as input; instead, the seed is
 * extracted, in some manner or another, from the hardware by this function.
 *
 * The EDN must be initialized before calling this function, since it uses the
 * Ibex RND interface and will wait until entropy is available.
 *
 * @param rnd Function to call for fresh randomness.
 * @param ctx The context to initialize.
 * @param min_len The minimum length this traversal order must visit.
 */
void random_order_init(random_order_t *ctx, size_t min_len);

/**
 * Returns the length of the sequence represented by `ctx`.
 *
 * This value may be greater than `min_len` specified in
 * `random_order_init()`, but the sequence is guaranteed to contain every
 * integer in `0..min_len`.
 *
 * This value represents the number of times `random_order_advance()` may be
 * called.
 *
 * @param ctx The context to query.
 * @return The length of the sequence.
 */
size_t random_order_len(const random_order_t *ctx);

/**
 * Returns the next element in the sequence represented by `ctx`.
 *
 * See `random_order_len()` for discovering how many times this function can
 * be called.
 *
 * @param ctx The context to advance.
 * @return The next value in the sequence.
 */
size_t random_order_advance(random_order_t *ctx);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_RANDOM_ORDER_H_
