// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_VERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/error.h"
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
 * A type that holds precomputed Montgomery constants for a RSA-3072 public
 * key.
 *
 * The constants are:
 *  rr : (2^3072)^2 mod n
 *  m0_inv : (-(n^(-1))) mod 2^256
 */
typedef struct rsa_3072_constants_t {
  rsa_3072_int_t rr;
  uint32_t m0_inv[kOtbnWideWordNumWords];
} rsa_3072_constants_t;

/**
 * Computes Montgomery constant R^2 for an RSA-3072 public key.
 *
 * @param public_key Key for which to compute constants.
 * @param result Buffer in which to store output
 * @return Result of the operation (OK or error).
 */
otbn_error_t rsa_3072_compute_rr(const rsa_3072_public_key_t *public_key,
                                 rsa_3072_int_t *result);

/**
 * Computes Montgomery constant m0_inv for an RSA-3072 public key.
 *
 * @param public_key Key for which to compute constants.
 * @param result Buffer in which to store output
 * @return Result of the operation (OK or error).
 */
otbn_error_t rsa_3072_compute_m0_inv(const rsa_3072_public_key_t *public_key,
                                     uint32_t result[kOtbnWideWordNumWords]);

/**
 * Computes Montgomery constants for an RSA-3072 public key.
 *
 * @param public_key Key for which to compute constants.
 * @param result Buffer in which to store output
 * @return Result of the operation (OK or error).
 */
otbn_error_t rsa_3072_compute_constants(const rsa_3072_public_key_t *public_key,
                                        rsa_3072_constants_t *result);

/**
 * Verifies an RSA-3072 signature.
 *
 * @param signature Signature to be verified.
 * @param message Digest of the message to check the signature against.
 * @param public_key Key to check the signature against.
 * @param result Buffer in which to store output (true iff signature is valid)
 * @return Result of the operation (OK or error).
 */
otbn_error_t rsa_3072_verify(const rsa_3072_int_t *signature,
                             const rsa_3072_int_t *message,
                             const rsa_3072_public_key_t *public_key,
                             const rsa_3072_constants_t *constants,
                             hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_VERIFY_H_
