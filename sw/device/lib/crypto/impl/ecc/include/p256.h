// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_P256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_P256_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of a P-256 curve point coordinate in bits (modulo p).
   */
  kP256CoordBits = 256,
  /**
   * Length of a P-256 curve point coordinate in bytes.
   */
  kP256CoordBytes = kP256CoordBits / 8,
  /**
   * Length of a P-256 curve point coordinate in words.
   */
  kP256CoordWords = kP256CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the P-256 scalar field (modulo the curve order n).
   */
  kP256ScalarBits = 256,
  /**
   * Length of a secret scalar share in bytes.
   */
  kP256ScalarBytes = kP256ScalarBits / 8,
  /**
   * Length of secret scalar share in words.
   */
  kP256ScalarWords = kP256ScalarBytes / sizeof(uint32_t),
  /**
   * Length of a masked secret scalar share.
   *
   * This implementation uses extra redundant bits for side-channel protection.
   */
  kP256MaskedScalarShareBits = kP256ScalarBits + 64,
  /**
   * Length of a masked secret scalar share in bytes.
   */
  kP256MaskedScalarShareBytes = kP256MaskedScalarShareBits / 8,
  /**
   * Length of masked secret scalar share in words.
   */
  kP256MaskedScalarShareWords = kP256MaskedScalarShareBytes / sizeof(uint32_t),
  /**
   * Number of shares for the scalar.
   */
  kP256MaskedScalarNumShares = 2,
  /**
   * Length of the full masked secret scalar share in bits.
   */
  kP256MaskedScalarTotalShareBits =
      kP256MaskedScalarNumShares * kP256MaskedScalarShareBits,
  /**
   * Length of the full masked secret scalar share in bytes.
   */
  kP256MaskedScalarTotalShareBytes =
      kP256MaskedScalarNumShares * kP256MaskedScalarShareBytes,
  /**
   * Length of the full masked secret scalar share in words.
   */
  kP256MaskedScalarTotalShareWords =
      kP256MaskedScalarNumShares * kP256MaskedScalarShareWords,
};

/**
 * A type that holds a masked value from the P-256 scalar field.
 *
 * This struct is used to represent secret keys, which are integers modulo n.
 * The key d is represented in two 320-bit shares, d0 and d1, such that d = (d0
 * + d1) mod n. Mathematically, d0 and d1 could also be reduced modulo n, but
 * the extra bits provide side-channel protection.
 */
typedef struct p256_masked_scalar {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[kP256MaskedScalarShareWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[kP256MaskedScalarShareWords];
  /**
   * Checksum over share0.
   */
  uint32_t checksum;
} p256_masked_scalar_t;

/**
 * A type that holds a P-256 curve point.
 */
typedef struct p256_point {
  /**
   * Affine x-coordinate.
   */
  uint32_t x[kP256CoordWords];
  /**
   * Affine y-coordinate.
   */
  uint32_t y[kP256CoordWords];
} p256_point_t;

/**
 * A type that holds an ECDSA/P-256 signature.
 *
 * The signature consists of two integers r and s, computed modulo n.
 */
typedef struct p256_ecdsa_signature_t {
  uint32_t r[kP256ScalarWords];
  uint32_t s[kP256ScalarWords];
} p256_ecdsa_signature_t;

/**
 * A type that holds a blinded ECDH shared secret key.
 *
 * The key is boolean-masked (XOR of the two shares).
 */
typedef struct p256_ecdh_shared_key {
  uint32_t share0[kP256CoordWords];
  uint32_t share1[kP256CoordWords];
  // Checksum over share0.
  uint32_t checksum;
} p256_ecdh_shared_key_t;

/**
 * Compute the checksum of an p256 masked scalar.
 *
 * Call this routine after creating or modifying the p256 scalar structure.
 *
 * @param key p256 masked scalar.
 * @returns Checksum value.
 */
uint32_t p256_masked_scalar_checksum(const p256_masked_scalar_t *scalar);

/**
 * Perform an integrity check on the p256 masked scalar.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key p256 masked scalar.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t p256_masked_scalar_checksum_check(
    const p256_masked_scalar_t *scalar);

/**
 * Compute the checksum of an p256 ecdh key.
 *
 * Call this routine after creating or modifying the p256 key structure.
 *
 * @param key p256 ecdh shared key.
 * @returns Checksum value.
 */
uint32_t p256_ecdh_shared_key_checksum(const p256_ecdh_shared_key_t *key);

/**
 * Perform an integrity check on the p256 ecdh key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key p256 ecdh shared key.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t p256_ecdh_shared_key_checksum_check(
    const p256_ecdh_shared_key_t *key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_P256_H_
