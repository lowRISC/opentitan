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
   * Length of an RSA-3072 modulus or signature in words.
   */
  kSigVerifyRsaNumWords = kSigVerifyRsaNumBits / (sizeof(uint32_t) * 8),
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

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_KEY_H_
