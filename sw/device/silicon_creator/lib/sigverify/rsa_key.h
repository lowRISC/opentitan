// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_KEY_H_

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
   * Length of an RSA-3072 modulus or signature in bytes.
   */
  kSigVerifyRsaNumBytes = kSigVerifyRsaNumBits / 8,
  /**
   * Length of an RSA-3072 modulus or signature in words.
   */
  kSigVerifyRsaNumWords = kSigVerifyRsaNumBytes / sizeof(uint32_t),
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
 * An RSA public key with exponent 65537.
 */
typedef struct sigverify_rsa_key {
  /**
   * Modulus, a `kSigVerifyRsaNumWords` base 2^32 digit integer, little-endian.
   */
  sigverify_rsa_buffer_t n;
  /**
   * Negative of the multiplicative inverse of n modulo 2^256, little-endian.
   *
   * Calculations performed on OTBN (word size: 256 bits) use the whole array
   * while calculations performed on Ibex (word size: 32 bits) use only the
   * first word, which is equal to -n^-1 mod 2^32.
   */
  uint32_t n0_inv[8];
} sigverify_rsa_key_t;

/**
 * Gets the ID of an RSA public key from its modulus.
 *
 * ID of a key is the least significant word of its modulus.
 * Callers must make sure that `modulus` is valid before calling this function.
 *
 * @param key An RSA public key.
 * @return ID of the key.
 */
inline uint32_t sigverify_rsa_key_id_get(
    const sigverify_rsa_buffer_t *modulus) {
  return modulus->data[0];
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_KEY_H_
