// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_MODEXP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_MODEXP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/otbn_util.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /* Length of the RSA-3072 modulus is 3072 bits */
  kRsa3072NumBits = 3072,
  /* Length of the RSA-3072 modulus in words */
  kRsa3072NumWords = kRsa3072NumBits / (sizeof(uint32_t) * 8),
};

/**
 * A type that holds an element of the RSA-3072 finite field (i.e. a 3072-bit
 * number).
 *
 * This type can be used for RSA-3072 signatures, keys, and intermediate values
 * during modular exponentiation.
 */
typedef struct rsa_3072_int_t {
  uint32_t data[kRsa3072NumWords];
} rsa_3072_int_t;

/**
 * A type that holds an RSA-3072 public key.
 *
 * The public key consists of a 3072-bit modulus n and a public exponent e.
 */
typedef struct rsa_3072_public_key_t {
  rsa_3072_int_t n;
  uint32_t e;
} rsa_3072_public_key_t;

/**
 * Performs modular exponentiation for signature verification.
 *
 * Computes (signature^e) mod n, where e and n are the exponent and modulus in
 * the public key respectively.
 *
 * Currently, only e=65537 is supported.
 *
 * @param signature Signature to be verified.
 * @param public_key Key to check the signature against.
 * @param m0_inv Precomputed Montgomery constant ((-(n^-1)) mod 2^256)
 * @param recoveredMessage Buffer in which to store output
 * @return Result of the operation (OK or error).
 */
otbn_error_t run_otbn_rsa_3072_modexp(const rsa_3072_int_t *signature,
                                      const rsa_3072_public_key_t *public_key,
                                      const uint32_t *m0_inv,
                                      rsa_3072_int_t *recovered_message);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_MODEXP_H_
