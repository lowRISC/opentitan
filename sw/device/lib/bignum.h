// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BIGNUM_H_
#define OPENTITAN_SW_DEVICE_LIB_BIGNUM_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * A non-negative bignum representation in little-endian byte order. Calling any
 * function in this header with two or more arguments that point to different
 * 'bignum_t's with overlapping words[0..len] regions is cause for undefined
 * behavior.
 */
typedef struct bignum {
  /**
   * The underlying buffer that contains the little-endian representation of
   * bignum.
   */
  uint32_t *words;

  /**
   * The number of words in the bignum.
   */
  size_t len;
} bignum_t;

typedef struct bignum_ctx {
  uint32_t *buffer;
  size_t len;
  size_t cappacity;
} bignum_ctx_t;

typedef enum bignum_result {
  kBignumOk = 0,
  kBignumError,
  kBignumBadArgs,
  kBignumOutOfBounds,
  kBignumOverflow,
  kBignumUnderflow,
  kBignumOutOfMemory,
} bignum_result_t;

typedef enum bignum_cmp_result {
  kBignumCmpEq = kBignumOk,
  kBignumCmpError = kBignumError,
  kBignumCmpBadArgs = kBignumBadArgs,
  kBignumCmpOutOfBounds = kBignumOutOfBounds,
  kBignumCmpGt,
  kBignumCmpLt,
} bignum_cmp_result_t;

/**
 * Initializes a `bignum_t`.
 */
bignum_result_t bignum_init(bignum_t *bn, uint32_t *words, size_t len);

/**
 * Compute r = a * b.
 *
 * Both `r` and `a` may reference the same `bignum_t`.
 */
bignum_result_t bignum_mul_word(bignum_t *r, const bignum_t *a, uint32_t b);

/**
 * Compute r = a - b
 */
bignum_result_t bignum_sub(bignum_t *r, const bignum_t *a, const bignum_t *b);

/**
 * Compare a to b.
 */
bignum_cmp_result_t bignum_cmp(const bignum_t *a, const bignum_t *b);

/**
 * Computes a^-1 mod 2^32 for odd values of a. This is used in montgomery
 * multiplication.
 */
uint32_t bignum_mont_mod_inverse(uint32_t a);

/**
 * Computes r = a * R mod n, where R = 2**(BIGNUM_NUM_WORDS * WORD_SIZE).
 *
 * In other words, computes the montgomery reduction of `a` modulo `n` with
 * respect to R = 2 ^ (bitlength of n + 1).
 */
bignum_result_t bignum_to_montgomery(bignum_t *r, const bignum_t *a,
    const bignum_t *n);

/**
 * Computes r = a*b*R mod n, which is the same as r = aR * bR * (1/R) mod n.
 */
bignum_result_t bignum_mul_montgomery(bignum_t *r, const bignum_t *aR,
    const bignum_t *bR, const bignum_t *n, uint32_t n_inv);

/**
 * Computes r = a^e mod n.
 */
bignum_result_t bignum_mod_exp_by_word(bignum_t *r, const bignum_t *a,
    uint32_t e, const bignum_t *n, bignum_ctx_t *ctx);

#endif  // OPENTITAN_SW_DEVICE_LIB_BIGNUM_H_
