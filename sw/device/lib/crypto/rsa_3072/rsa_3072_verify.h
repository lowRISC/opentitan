// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_VERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /* Length of the RSA-3072 modulus is 3072 bits */
  kRsa3072NumBits = 3072,
  /* Length of the RSA-3072 modulus in bytes */
  kRsa3072NumBytes = kRsa3072NumBits / 8,
  /* Length of the RSA-3072 modulus in words */
  kRsa3072NumWords = kRsa3072NumBytes / sizeof(uint32_t),
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
  uint8_t m0_inv[kOtbnWlenBytes];
} rsa_3072_constants_t;

/**
 * Computes Montgomery constants for an RSA-3072 public key.
 *
 * @param otbn OTBN context.
 * @param public_key Key for which to compute constants.
 * @param result Buffer in which to store output
 * @return Result of the operation (OK or error).
 */
otbn_result_t rsa_3072_compute_constants(
    otbn_t *otbn, const rsa_3072_public_key_t *public_key,
    rsa_3072_constants_t *result);

/**
 * Encode the message according to RFC 8017, section 9.2, with a SHA2-256 hash
 * function. See https://datatracker.ietf.org/doc/html/rfc8017#section-9.2
 *
 * Returns the dif result from the HMAC device.
 *
 * Note that because we know the length of the modulus is 3072 bits, we know
 * that emLen (the intended length in bytes of the message representative) is
 * 3072/8 = 384, so it is not an argument here.
 *
 * Unlike in RFC 8017, the message representative returned here is in
 * little-endian form.
 *
 * `msg` must point to an allocated array of at least `msg_len` bytes.
 *
 * @param otbn OTBN context.
 * @param msg Message to encode
 * @param msg_len Length of the message in bytes
 * @param result Resulting 3072-bit message representative
 * @return Result of the operation (OK or error).
 */
dif_result_t rsa_3072_encode_sha256(const dif_hmac_t *hmac, const uint8_t *msg,
                                    size_t msg_len, rsa_3072_int_t *result);

/**
 * Verifies an RSA-3072 signature.
 *
 * @param otbn OTBN context.
 * @param signature Signature to be verified.
 * @param message Encoded message to check the signature against (little-endian)
 * @param public_key Key to check the signature against.
 * @param result Buffer in which to store output (true iff signature is valid)
 * @return Result of the operation (OK or error).
 */
otbn_result_t rsa_3072_verify(otbn_t *otbn, const rsa_3072_int_t *signature,
                              const rsa_3072_int_t *message,
                              const rsa_3072_public_key_t *public_key,
                              const rsa_3072_constants_t *constants,
                              hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRYPTO_RSA_3072_RSA_3072_VERIFY_H_
