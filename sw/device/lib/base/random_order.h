// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_RANDOM_ORDER_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_RANDOM_ORDER_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief Functions for generating random traversal orders.
 */

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
  size_t state;
  size_t max;
} random_order_t;

/**
 * Constructs a new, randomly-seeded traversal order,
 * running from `0` to at least `min_len`.
 *
 * This function does not take a seed as input; instead, the seed is
 * extracted, in some manner or another, from the hardware by this function.
 *
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
