// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECDSA_P256_ECDSA_P256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECDSA_P256_ECDSA_P256_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of a P-256 curve point coordinate in bits (integer modulo the "p"
   * parameter, see FIPS 186-4 section D.1.2.3)
   */
  kP256CoordNumBits = 256,
  /* Length of a P-256 curve point coordinate in words */
  kP256CoordNumWords = kP256CoordNumBits / (sizeof(uint32_t) * 8),
  /**
   * Length of a number modulo the P-256 "n" parameter (see FIPS 186-4 section
   * D.1.2.3) in bits
   */
  kP256ScalarNumBits = 256,
  /* Length of a number modulo the P-256 "n" parameter in words */
  kP256ScalarNumWords = kP256ScalarNumBits / (sizeof(uint32_t) * 8),
  /* Length of the message digest in bits */
  kP256MessageDigestNumBits = 256,
};

/**
 * A type that holds an ECDSA/P-256 signature.
 *
 * The signature consists of two integers r and s, computed modulo n.
 */
typedef struct ecdsa_p256_signature_t {
  uint32_t r[kP256ScalarNumWords];
  uint32_t s[kP256ScalarNumWords];
} ecdsa_p256_signature_t;

/**
 * A type that holds an ECDSA/P-256 private key.
 *
 * The private key consists of a single integer d, computed modulo n. The key
 * is represented in two shares, d0 and d1, such that d = (d0 + d1) mod n. The
 * shares d0 and d1 are also both computed modulo n.
 */
typedef struct ecdsa_p256_private_key_t {
  uint32_t d0[kP256ScalarNumWords];
  uint32_t d1[kP256ScalarNumWords];
} ecdsa_p256_private_key_t;

/**
 * A type that holds an ECDSA/P-256 public key.
 *
 * The public key is a point Q on the p256 curve, consisting of two coordinates
 * x and y computed modulo p.
 */
typedef struct ecdsa_p256_public_key_t {
  uint32_t x[kP256CoordNumWords];
  uint32_t y[kP256CoordNumWords];
} ecdsa_p256_public_key_t;

/**
 * A type that holds an ECDSA/P-256 message digest.
 *
 * The message digest is expected to already be transformed into an integer
 * h = H(msg) mod n, where H is the hash function.
 */
typedef struct ecdsa_p256_message_digest_t {
  uint32_t h[kP256ScalarNumWords];
} ecdsa_p256_message_digest_t;

/**
 * Generates an ECDSA/P-256 signature.
 *
 * @param message_digest Digest of the message to sign.
 * @param private_key Key to sign the message with.
 * @param result Buffer in which to store the generated signature.
 * @return Result of the operation (OK or error).
 */
otbn_error_t ecdsa_p256_sign(const ecdsa_p256_message_digest_t *digest,
                             const ecdsa_p256_private_key_t *private_key,
                             ecdsa_p256_signature_t *result);

/**
 * Verifies an ECDSA/P-256 signature.
 *
 * @param signature Signature to be verified.
 * @param message_digest Digest of the message to check the signature against.
 * @param public_key Key to check the signature against.
 * @param result Buffer in which to store output (true iff signature is valid)
 * @return Result of the operation (OK or error).
 */
otbn_error_t ecdsa_p256_verify(const ecdsa_p256_signature_t *signature,
                               const ecdsa_p256_message_digest_t *digest,
                               const ecdsa_p256_public_key_t *public_key,
                               hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECDSA_P256_ECDSA_P256_H_
