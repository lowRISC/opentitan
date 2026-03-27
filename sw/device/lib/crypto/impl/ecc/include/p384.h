// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_P384_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_P384_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of a P-384 curve point coordinate in bits (modulo p).
   */
  kP384CoordBits = 384,
  /**
   * Length of a P-384 curve point coordinate in bytes.
   */
  kP384CoordBytes = kP384CoordBits / 8,
  /**
   * Length of a P-384 curve point coordinate in words.
   */
  kP384CoordWords = kP384CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the P-384 scalar field (modulo the curve order n).
   */
  kP384ScalarBits = 384,
  /**
   * Length of a secret scalar share in bytes.
   */
  kP384ScalarBytes = kP384ScalarBits / 8,
  /**
   * Length of secret scalar share in words.
   */
  kP384ScalarWords = kP384ScalarBytes / sizeof(uint32_t),
  /**
   * Length of a masked secret scalar share.
   *
   * This implementation uses extra redundant bits for side-channel protection.
   */
  kP384MaskedScalarShareBits = kP384ScalarBits + 64,
  /**
   * Length of a masked secret scalar share in bytes.
   */
  kP384MaskedScalarShareBytes = kP384MaskedScalarShareBits / 8,
  /**
   * Length of masked secret scalar share in words.
   */
  kP384MaskedScalarShareWords = kP384MaskedScalarShareBytes / sizeof(uint32_t),
  /**
   * Number of shares for the scalar.
   */
  kP384MaskedScalarNumShares = 2,
  /**
   * Length of the full masked secret scalar share in bits.
   */
  kP384MaskedScalarTotalShareBits =
      kP384MaskedScalarNumShares * kP384MaskedScalarShareBits,
  /**
   * Length of the full masked secret scalar share in bytes.
   */
  kP384MaskedScalarTotalShareBytes =
      kP384MaskedScalarNumShares * kP384MaskedScalarShareBytes,
  /**
   * Length of the full masked secret scalar share in words.
   */
  kP384MaskedScalarTotalShareWords =
      kP384MaskedScalarNumShares * kP384MaskedScalarShareWords,
};

/**
 * A type that holds a masked value from the P-384 scalar field.
 *
 * This struct is used to represent secret keys, which are integers modulo n.
 * The key d is represented in two 320-bit shares, d0 and d1, such that d = (d0
 * + d1) mod n. Mathematically, d0 and d1 could also be reduced modulo n, but
 * the extra bits provide side-channel protection.
 */
typedef struct p384_masked_scalar {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[kP384MaskedScalarShareWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[kP384MaskedScalarShareWords];
  /**
   * Checksum over share0.
   */
  uint32_t checksum;
} p384_masked_scalar_t;

/**
 * A type that holds a P-384 curve point.
 */
typedef struct p384_point {
  /**
   * Affine x-coordinate.
   */
  uint32_t x[kP384CoordWords];
  /**
   * Affine y-coordinate.
   */
  uint32_t y[kP384CoordWords];
} p384_point_t;

/**
 * A type that holds an ECDSA/P-384 signature.
 *
 * The signature consists of two integers r and s, computed modulo n.
 */
typedef struct p384_ecdsa_signature_t {
  uint32_t r[kP384ScalarWords];
  uint32_t s[kP384ScalarWords];
} p384_ecdsa_signature_t;

/**
 * A type that holds a blinded ECDH shared secret key.
 *
 * The key is boolean-masked (XOR of the two shares).
 */
typedef struct p384_ecdh_shared_key {
  uint32_t share0[kP384CoordWords];
  uint32_t share1[kP384CoordWords];
  // Checksum over share0.
  uint32_t checksum;
} p384_ecdh_shared_key_t;

/**
 * Compute the checksum of an p384 masked scalar.
 *
 * Call this routine after creating or modifying the p384 scalar structure.
 *
 * @param key p384 masked scalar.
 * @returns Checksum value.
 */
uint32_t p384_masked_scalar_checksum(const p384_masked_scalar_t *scalar);

/**
 * Perform an integrity check on the p384 masked scalar.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key p384 masked scalar.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t p384_masked_scalar_checksum_check(
    const p384_masked_scalar_t *scalar);

/**
 * Compute the checksum of an p384 ecdh key.
 *
 * Call this routine after creating or modifying the p384 key structure.
 *
 * @param key p384 ecdh shared key.
 * @returns Checksum value.
 */
uint32_t p384_ecdh_shared_key_checksum(const p384_ecdh_shared_key_t *key);

/**
 * Perform an integrity check on the p384 ecdh key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key p384 ecdh shared key.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t p384_ecdh_shared_key_checksum_check(
    const p384_ecdh_shared_key_t *key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_INCLUDE_P384_H_
