// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/mod_exp_ibex.h"

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

/**
 * Subtracts the modulus of `key` from `a` in-place, i.e. `a -= n`.
 *
 * Since `a` can be smaller than the modulus, this function also returns the
 * borrow.
 *
 * @param key An RSA public key.
 * @param[in,out] a Buffer that holds `a`, little-endian.
 * @return Borrow.
 */
static uint32_t subtract_modulus(const sigverify_rsa_key_t *key,
                                 sigverify_rsa_buffer_t *a) {
  uint32_t borrow = 0;
  for (size_t i = 0; i < ARRAYSIZE(a->data); ++i) {
    uint32_t temp = a->data[i] - borrow;
    // We borrow if either the above or the below subtraction wraps around.
    // Note: borrow can only be 0 or 1.
    borrow = (a->data[i] < borrow) + (temp < key->n.data[i]);
    a->data[i] = temp - key->n.data[i];
  }
  return borrow;
}

/**
 * Checks if `a` is greater than or equal to the modulus of `key`.
 *
 * @param key An RSA public key.
 * @param a Buffer that holds `a`, little-endian.
 * @return Comparison result.
 */
static bool greater_equal_modulus(const sigverify_rsa_key_t *key,
                                  const sigverify_rsa_buffer_t *a) {
  // Note: Loop terminates when `i` wraps around.
  for (size_t i = ARRAYSIZE(a->data) - 1; i < ARRAYSIZE(a->data); --i) {
    if (a->data[i] != key->n.data[i]) {
      return a->data[i] > key->n.data[i];
    }
  }
  return true;
}

/**
 * Shifts `a` left one bit in-place, i.e. `a <<= 1`.
 *
 * Since the result may not fit in `a`, this function also returns the most
 * significant bit of the result.
 *
 * @param[in,out] a Buffer that holds `a`, little-endian.
 * @return Most significant bit of the result.
 */
static uint32_t shift_left(sigverify_rsa_buffer_t *a) {
  const uint32_t msb = a->data[ARRAYSIZE(a->data) - 1] >> 31;
  for (size_t i = ARRAYSIZE(a->data) - 1; i > 0; --i) {
    a->data[i] = (a->data[i] << 1) | (a->data[i - 1] >> 31);
  }
  a->data[0] <<= 1;
  return msb;
}

/**
 * Computes the Montgomery reduction of the product of two integers.
 *
 * Given an RSA public key, x, and y this function computes x*y*R^-1 mod n,
 * where
 * - x and y are integers with `kSigVerifyRsaNumWords` base 2^32 digits,
 * - n is the modulus of the key, and
 * - R is 2^`kSigVerifyRsaNumBits`, e.g. 2^3072 for RSA-3072.
 *
 * See Handbook of Applied Cryptography, Ch. 14, Alg. 14.36.
 *
 * @param key An RSA public key.
 * @param x Buffer that holds `x`, little-endian.
 * @param y Buffer that holds `y`, little-endian.
 * @param[out] result Buffer to write the result to, little-endian.
 */
static void mont_mul(const sigverify_rsa_key_t *key,
                     const sigverify_rsa_buffer_t *x,
                     const sigverify_rsa_buffer_t *y,
                     sigverify_rsa_buffer_t *result) {
  memset(result->data, 0, sizeof(result->data));

  for (size_t i = 0; i < ARRAYSIZE(x->data); ++i) {
    // The loop below reads one word ahead of writes to avoid a separate loop
    // for the division by `b` in step 2.2 of the algorithm. Thus, `acc0` and
    // `acc1` are initialized here before the loop. `acc0` holds the sum of
    // first two addends in step 2.2 while `acc1` holds the entire sum. Carries
    // of these operations are stored separately in the upper words of `acc0`
    // and `acc1`. `acc0` and `acc1` can safely store these intermediate values,
    // i.e. without wrapping, because UINT32_MAX^2 + 2*UINT32_MAX is
    // 0xffff_ffff_ffff_ffff.

    // Holds the sum of the first two addends in step 2.2.
    uint64_t acc0 = (uint64_t)x->data[i] * y->data[0] + result->data[0];
    const uint32_t u_i = (uint32_t)acc0 * key->n0_inv[0];
    // Holds the sum of the all three addends in step 2.2.
    uint64_t acc1 = (uint64_t)u_i * key->n.data[0] + (uint32_t)acc0;

    // Process the i^th digit of `x`, i.e. `x[i]`.
    for (size_t j = 1; j < ARRAYSIZE(result->data); ++j) {
      acc0 = (uint64_t)x->data[i] * y->data[j] + result->data[j] + (acc0 >> 32);
      acc1 = (uint64_t)u_i * key->n.data[j] + (uint32_t)acc0 + (acc1 >> 32);
      result->data[j - 1] = (uint32_t)acc1;
    }
    acc0 = (acc0 >> 32) + (acc1 >> 32);
    result->data[ARRAYSIZE(result->data) - 1] = (uint32_t)acc0;

    // The intermediate result of this algorithm before the check below is
    // bounded by R + n (Eq. (4) in Montgomery Arithmetic from a Software
    // Perspective, Bos. J. W, Montgomery, P. L.) where n is the modulus of
    // `key` and n < R. Therefore, if there is a carry, then `result` is not the
    // least non-negative residue of x*y*R^-1 mod n. Since `acc0 >> 32` here is
    // at most 1, we can subtract the modulus from `result` without taking it
    // into account and fit `result` into `kSigVerifyRsaNumWords`. Since this is
    // not a direct comparison with the modulus, the final result is not
    // guaranteed to be the least non-negative residue of x*y*R^-1 mod n.
    if (acc0 >> 32) {
      subtract_modulus(key, result);
    }
  }
}

/**
 * Calculates R^2 mod n, where R = 2^kSigVerifyRsaNumBits.
 *
 * @param key An RSA public key.
 * @param[out] result Buffer to write the result to, little-endian.
 */
static void calc_r_square(const sigverify_rsa_key_t *key,
                          sigverify_rsa_buffer_t *result) {
  sigverify_rsa_buffer_t buf;
  memset(buf.data, 0, sizeof(result->data));
  // This subtraction sets buf = -n mod R = R - n, which is equivalent to R
  // modulo n and ensures that `buf` fits in `kSigVerifyRsaNumWords` going
  // into the loop.
  subtract_modulus(key, &buf);

  // Compute (2^96 * R) mod n.
  // Each run of the loop doubles buf and reduces modulo n.
  for (size_t i = 0; i < 96; ++i) {
    uint32_t msb = shift_left(&buf);
    // Reduce until buf < n. Doing this at every iteration minimizes the
    // total number of subtractions that we need to perform.
    while (msb > 0 || greater_equal_modulus(key, &buf)) {
      msb -= subtract_modulus(key, &buf);
    }
  }

  // Perform 5 montgomery squares to get RR = ((2^96)^32 * R) mod n
  mont_mul(key, &buf, &buf, result);
  for (size_t i = 0; i < 2; ++i) {
    mont_mul(key, result, result, &buf);
    mont_mul(key, &buf, &buf, result);
  }
}

rom_error_t sigverify_mod_exp_ibex(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result) {
  // Reject the signature if it is too large (n <= sig): RFC 8017, section
  // 5.2.2, step 1.
  if (greater_equal_modulus(key, sig)) {
    return kErrorSigverifyLargeRsaSignature;
  }

  sigverify_rsa_buffer_t buf;

  // result = R^2 mod n
  calc_r_square(key, result);
  // buf = sig * R mod n
  mont_mul(key, sig, result, &buf);
  for (size_t i = 0; i < 8; ++i) {
    // result = sig^{2*4^i} * R mod n (sig's exponent: 2, 8, 32, ..., 32768)
    mont_mul(key, &buf, &buf, result);
    // buf = sig^{4^{i+1}} * R mod n (sig's exponent: 4, 16, 64, ..., 65536)
    mont_mul(key, result, result, &buf);
  }
  // result = sig^65537 mod n
  mont_mul(key, &buf, sig, result);

  // We need this check because the result of `mont_mul` is not guaranteed to be
  // the least non-negative residue. We need to subtract the modulus n from
  // `result` at most once because R/2 < n < R.
  if (greater_equal_modulus(key, result)) {
    subtract_modulus(key, result);
  }

  return kErrorOk;
}
