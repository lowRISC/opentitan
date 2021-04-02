// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of words of the modulus and signature for RSA-3072.
   */
  kRsaNumWords = 96,
};

// FIXME: Make static and move this comment to the source file. This is here
// just to be able to add a simple test.
/**
 * Computes the Montgomery reduction of the product of two integers.
 *
 * Given x, y, m, and m', this function computes x*y*R^-1 mod m, where
 * - x, y, and m are integers with kRsaNumWords base 2^32 digits,
 * - m' = -m^-1 mod b,
 * - R is (2^32)^kRsaNumWords, e.g. 2^3072 for RSA-3072, and
 * - b is 2^32.
 *
 * See Handbook of Applied Cryptography, Ch. 14, Alg. 14.36.
 *
 * @param x A `kRsaNumWords` long buffer, little-endian.
 * @param y A `kRsaNumWords` long buffer, little-endian.
 * @param m A `kRsaNumWords` long buffer, little-endian.
 * @param m_prime Negative of the multiplicative inverse of m modulo b.
 * @param[out] result A `kRsaNumWords` long buffer, little-endian.
 */
void mont_mul(const uint32_t *x, const uint32_t *y, const uint32_t *m,
              uint32_t m_prime, uint32_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_
