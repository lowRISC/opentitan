// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIG_VERIFY_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIG_VERIFY_KEYS_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of an RSA-3072 modulus or signature in bits.
   */
  kSigVerifyRsaNumBits = 3072,
  /**
   * Length of an RSA-3072 modulus or signature in words.
   */
  kSigVerifyRsaNumWords = kSigVerifyRsaNumBits / (sizeof(uint32_t) * 8),
  /**
   * Number of RSA public keys.
   */
  kSigVerifyNumRsaKeys = 2,
};

/**
 * A type that holds `kSigVerifyRsaNumWords` words.
 *
 * This can be used for RSA-3072 moduli, signatures, and intermediate values
 * during modular exponentiation.
 */
typedef struct sigverify_rsa_buffer {
  uint32_t data[kSigVerifyRsaNumWords];
} sigverify_rsa_buffer_t;

/**
 * An RSA public key.
 *
 * Note: Defined here to be able to use in tests.
 */
typedef struct sigverify_rsa_key {
  /**
   * Modulus, a `kSigVerifyRsaNumWords` base 2^32 digit integer, little-endian.
   */
  sigverify_rsa_buffer_t n;
  /**
   * Negative of the multiplicative inverse of n modulo 2^32.
   */
  uint32_t n0_inv;
  /**
   * Exponent.
   */
  uint32_t exponent;
} sigverify_rsa_key_t;

/**
 * Public keys for signature verification.
 *
 * Note: Declared here to be able to use in tests.
 */
extern const sigverify_rsa_key_t kSigVerifyRsaKeys[kSigVerifyNumRsaKeys];

/**
 * Gets the ID of an RSA public key.
 *
 * ID of a key is the least significant byte of its modulus.
 * Callers must make sure that `key` is valid before calling this function.
 *
 * @param key An RSA public key.
 * @return ID of the key.
 */
inline uint32_t sigverify_rsa_key_id_get(const sigverify_rsa_key_t *key) {
  return key->n.data[0];
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIG_VERIFY_KEYS_H_
