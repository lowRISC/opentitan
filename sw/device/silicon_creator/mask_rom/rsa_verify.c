// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/rsa_verify.h"

#include <memory.h>
#include <stddef.h>

/**
 * Constants used in this file.
 */
enum {
  /**
   * Number of bits of RSA modulus.
   */
  kRsaNumBits = kRsaNumWords * sizeof(uint32_t) * 8,
};

/**
 * Subtracts `b` from `a` in-place, i.e. `a -= b`.
 *
 * Since a can be smaller than b, this function also returns the borrow.
 *
 * @param a A `kRsaNumWords` long buffer, little-endian.
 * @param b A `kRsaNumWords` long buffer, little-endian.
 * @return Borrow.
 */
static uint32_t subtract(uint32_t *a, const uint32_t *b) {
  uint32_t borrow = 0;
  for (size_t i = 0; i < kRsaNumWords; ++i) {
    uint64_t diff = (uint64_t)a[i] - b[i] - borrow;
    borrow = diff > a[i];
    a[i] = (uint32_t)diff;
  }
  return borrow;
}

/**
 * Checks if `a` is greater than or equal to `b`.
 *
 * @param a A `kRsaNumWords` long buffer, little-endian.
 * @param b A `kRsaNumWords` long buffer, little-endian.
 * @return Comparison result.
 */
static bool greater_equal(const uint32_t *a, const uint32_t *b) {
  // TODO(#33): Hardening?
  // Note: Loop terminates when `i` wraps around.
  for (size_t i = kRsaNumWords - 1; i < kRsaNumWords; --i) {
    if (a[i] != b[i]) {
      return a[i] > b[i];
    }
  }
  return true;
}

/**
 * Shifts `a` left one bit in-place, i.e. `a <<= 1`.
 *
 * Since the result may not fit in `kRsaNumWords`, this function also returns
 * the most significant bit of the result.
 *
 * @param a A `kRsaNumWords` long buffer, little-endian.
 * @return Most significant bit of the result.
 */
static uint32_t shift_left(uint32_t *a) {
  const uint32_t msb = a[kRsaNumWords - 1] >> 31;
  for (size_t i = kRsaNumWords - 1; i > 0; --i) {
    a[i] = (a[i] << 1) | (a[i - 1] >> 31);
  }
  a[0] <<= 1;
  return msb;
}

/**
 * Calculates R^2 mod m, where R = b^kRsaNumWords, and b is 2^32.
 *
 * @param m A `kRsaNumWords` long buffer, little-endian.
 * @param[out] result A `kRsaNumWords` long buffer, little-endian.
 */
static void calc_r_square(const uint32_t *m, uint32_t *result) {
  memset(result, 0, kRsaNumWords * sizeof(uint32_t));
  // Since R/2 < m < R, this subtraction ensures that result = R mod m and
  // fits in `kRsaNumWords` going into the loop.
  subtract(result, m);

  // Iteratively shift and reduce `result`.
  for (size_t i = 0; i < kRsaNumBits; ++i) {
    uint32_t msb = shift_left(result);
    // Reduce until result < m. Doing this at every iteration minimizes the
    // total number of subtractions that we need to perform.
    while (msb > 0 || greater_equal(result, m)) {
      msb -= subtract(result, m);
    }
  }
}

// FIXME: Merge this comment with the one in the header file.
// This function implements Alg. 14.36 in Handbook of Applied Cryptography:
// 1. result = 0
// 2. For i from 0 to (n - 1):
// 		2.1. u_i = (result_0 + x_i * y_0) * m' mod b
// 		2.2. result = (result + x_i * y + u_i * m) / b
// 3. If result >= m then result = result - m
// 4. Return result
void mont_mul(const uint32_t *x, const uint32_t *y, const uint32_t *m,
              const uint32_t m0_inv, uint32_t *result) {
  memset(result, 0, kRsaNumWords * sizeof(uint32_t));

  for (size_t i = 0; i < kRsaNumWords; ++i) {
    // The loop below reads one word ahead of writes to avoid a separate loop
    // for the division by `b` in step 2.2 of the algorithm. Thus, `acc0` and
    // `acc1` are initialized here before the loop. `acc0` holds the sum of
    // first two addends in step 2.2 while `acc1` holds the entire sum. Carries
    // of these operations are stored separately in the upper words of `acc0`
    // and `acc1`. `acc0` and `acc1` can safely store these intermediate values,
    // i.e. without wrapping, because UINT32_MAX^2 + 2*UINT32_MAX is
    // 0xffff_ffff_ffff_ffff.

    // Holds the sum of the first two addends in step 2.2.
    uint64_t acc0 = (uint64_t)x[i] * y[0] + result[0];
    const uint32_t u_i = (uint32_t)acc0 * m0_inv;
    // Holds the sum of the all three addends in step 2.2.
    uint64_t acc1 = (uint64_t)u_i * m[0] + (uint32_t)acc0;

    // Process the i^th digit of `x`, i.e. `x[i]`.
    for (size_t j = 1; j < kRsaNumWords; ++j) {
      acc0 = (uint64_t)x[i] * y[j] + result[j] + (acc0 >> 32);
      acc1 = (uint64_t)u_i * m[j] + (uint32_t)acc0 + (acc1 >> 32);
      result[j - 1] = (uint32_t)acc1;
    }
    acc0 = (acc0 >> 32) + (acc1 >> 32);
    result[kRsaNumWords - 1] = (uint32_t)acc0;

    // The intermediate result of this algorithm before the check below is
    // bounded by R + m (Eq. (4) in Montgomery Arithmetic from a Software
    // Perspective, Bos. J. W, Montgomery, P. L.) where `m` is an integer with
    // `kRsaNumWords` base 2^32 digits, `R` is 2^(`kRsaNumWords`*32), and m < R.
    // Therefore, if there is a carry, then `result` is not the least
    // non-negative residue of x*y*R^-1 mod m. Since `acc0 >> 32` here is at
    // most 1, we can subtract `m` from `result` without taking it into account
    // and fit `result` into `kRsaNumWords`. Since this is not a direct
    // comparison with `m`, the final result is not guaranteed to be the the
    // least non-negative residue of x*y*R^-1 mod m.
    if (acc0 >> 32) {
      subtract(result, m);
    }
  }
}

bool mod_exp(const uint32_t *sig, const rsa_verify_exponent_t e,
             const uint32_t *m, const uint32_t m0_inv, uint32_t *result) {
  uint32_t buf[kRsaNumWords];

  if (e == kRsaVerifyExponent3) {
    // buf = R^2 mod m
    calc_r_square(m, buf);
    // result = sig * R mod m
    mont_mul(sig, buf, m, m0_inv, result);
    // buf = sig^2 * R mod m
    mont_mul(result, result, m, m0_inv, buf);
  } else if (e == kRsaVerifyExponent65537) {
    // result = R^2 mod m
    calc_r_square(m, result);
    // buf = sig * R mod m
    mont_mul(sig, result, m, m0_inv, buf);
    for (size_t i = 0; i < 8; ++i) {
      // result = sig^{2*i+1} * R mod m (sig's exponent: 2, 8, 32, ..., 32768)
      mont_mul(buf, buf, m, m0_inv, result);
      // buf = sig^{4*i+2} * R mod m (sig's exponent: 4, 16, 64, ..., 65536)
      mont_mul(result, result, m, m0_inv, buf);
    }
  } else {
    return false;
  }
  // result = sig^e mod m
  mont_mul(buf, sig, m, m0_inv, result);

  // We need this check because the result of `mont_mul` is not guaranteed to be
  // the least non-negative residue. We need to subtract `m` from `result` at
  // most once because  `m` is the modulus of an RSA public key and therefore
  // R/2 < m < R.
  if (greater_equal(result, m)) {
    subtract(result, m);
  }

  return true;
}
