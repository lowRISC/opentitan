// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_

#include <stdbool.h>
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

/**
 * Exponent to use for signature verification.
 *
 * This determines the e in s^e mod n.
 */
// TODO(#22): May need to be updated after we decide on a key storage format.
typedef enum rsa_verify_exponent {
  /**
   * e = 3.
   */
  kRsaVerifyExponent3,
  /**
   * e = 65537.
   */
  kRsaVerifyExponent65537,
} rsa_verify_exponent_t;

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
 * @param m0_inv Negative of the multiplicative inverse of m modulo b.
 * @param[out] result A `kRsaNumWords` long buffer, little-endian.
 */
void mont_mul(const uint32_t *x, const uint32_t *y, const uint32_t *m,
              uint32_t m0_inv, uint32_t *result);

/**
 * Computes the modular exponentiation of an integer.
 *
 * Given sig, e, m, and m', this function computes sig^e mod m using Montgomery
 * multiplication, where
 * - sig and m are integers with kRsaNumWords base b digits,
 * - e is the exponent (3 or 65537),
 * - m' = -m^-1 mod b,
 * - b is 2^32.
 *
 * @param sig A `kRsaNumWords` long buffer, little-endian.
 * @param exponent Exponent to use for signature verification.
 * @param m A `kRsaNumWords` long buffer, little-endian.
 * @param m0_inv Negative of the multiplicative inverse of m modulo b.
 * @param[out] result A `kRsaNumWords` long buffer, little-endian.
 * @return True if successful, false otherwise.
 */
// TODO(#22): Update this after we decide on a key storage format.
// FIXME: Error codes are still under discussion, update after we reach a
// decision.
bool mod_exp(const uint32_t *sig, rsa_verify_exponent_t e, const uint32_t *m,
             uint32_t m0_inv, uint32_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_
