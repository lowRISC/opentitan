// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_CURVE25519_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_CURVE25519_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of words needed to encode a mode of operation.
   */
  kCurve25519ModeWords = 1,
  /**
   * Number of words needed to encode the verification result.
   */
  kCurve25519ResultWords = 1,
  /**
   * Number of words needed to hold an encoded point for Curve25519.
   */
  kCurve25519PointWords = 8,
  /**
   * Number of bytes needed to hold an encoded point for Curve25519.
   */
  kCurve25519PointBytes = kCurve25519PointWords * 4,
  /**
   * Number of bytes needed to hold a SHA512 hash.
   */
  kCurve25519HashBytes = 64,
  /**
   * Number of words needed to hold a SHA512 hash.
   */
  kCurve25519HashWords = kCurve25519HashBytes / 4,
  /**
   * Number of words needed to hold half of a SHA512 hash.
   */
  kCurve25519HalfHashWords = kCurve25519HashWords / 2,
  /**
   * Number of bytes needed to hold a encoded public or private key.
   */
  kCurve25519KeyBytes = 32,
  /**
   * Number of bytes needed to hold a scalar.
   */
  kCurve25519ScalarBytes = 32,
  /**
   * Number of words needed to hold a scalar.
   */
  kCurve25519ScalarWords = kCurve25519ScalarBytes / 4,
  /**
   * Number of bytes needed to hold a masked scalar s.
   */
  kCurve25519MaskedScalarSBytes = 48,
  /**
   * Number of words needed to hold a masked scalar s.
   */
  kCurve25519MaskedScalarSWords = kCurve25519MaskedScalarSBytes / 4,
  /**
   * Number of bytes needed to hold a masked scalar r.
   */
  kCurve25519MaskedScalarRBytes = 80,
  /**
   * Number of words needed to hold a masked scalar r.
   */
  kCurve25519MaskedScalarRWords = kCurve25519MaskedScalarRBytes / 4,
  /**
   * Number of zero padding words after a masked scalar share.
   */
  kCurve25519MaskedScalarPaddingWords = 4,
  /**
   * Length of a Curve25519 curve point coordinate in bits.
   */
  kCurve25519CoordBits = 256,
  /**
   * Length of a Curve25519 curve point coordinate in bytes.
   */
  kCurve25519CoordBytes = kCurve25519CoordBits / 8,
  /**
   * Length of a Curve25519 curve point coordinate in words.
   */
  kCurve25519CoordWords = kCurve25519CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the Curve25519 scalar field in bits.
   */
  kCurve25519ScalarBits = 256,
  /**
   * Length of a masked secret scalar share.
   *
   * Ed25519 uses no extra redundant bits for the initial seed sharing.
   */
  kCurve25519MaskedScalarShareBits = kCurve25519ScalarBits,
  /**
   * Length of a masked secret scalar share in bytes.
   */
  kCurve25519MaskedScalarShareBytes = kCurve25519MaskedScalarShareBits / 8,
  /**
   * Length of masked secret scalar share in words.
   */
  kCurve25519MaskedScalarShareWords =
      kCurve25519MaskedScalarShareBytes / sizeof(uint32_t),
  /**
   * Number of shares for the scalar.
   */
  kCurve25519MaskedScalarNumShares = 2,
  /**
   * Length of the full masked secret scalar share in bits.
   */
  kCurve25519MaskedScalarTotalShareBits =
      kCurve25519MaskedScalarNumShares * kCurve25519MaskedScalarShareBits,
  /**
   * Length of the full masked secret scalar share in bytes.
   */
  kCurve25519MaskedScalarTotalShareBytes =
      kCurve25519MaskedScalarNumShares * kCurve25519MaskedScalarShareBytes,
  /**
   * Length of the full masked secret scalar share in words.
   */
  kCurve25519MaskedScalarTotalShareWords =
      kCurve25519MaskedScalarNumShares * kCurve25519MaskedScalarShareWords,
};

/**
 * A type that holds an Ed25519 signature.
 *
 * The signature consists of a curve point R and a scalar S.
 */
typedef struct curve25519_signature_t {
  uint32_t r[kCurve25519PointWords];
  uint32_t s[kCurve25519ScalarWords];
} curve25519_signature_t;

/**
 * A type that holds the arithmetically masked shares of s.
 *
 * s is a 256-bit value secret scalar represesented by two 384-bit arithmetic
 * shares (s0, s1) such that s = s0 - s1.
 */
typedef struct curve25519_masked_scalar_s {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[kCurve25519MaskedScalarSWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[kCurve25519MaskedScalarSWords];
} curve25519_masked_scalar_s_t;

/**
 * A type that holds the arithmetically masked shares of r.
 *
 * s is a 512-bit value secret scalar represesented by two 640-bit arithmetic
 * shares (r0, r1) such that r = r0 - r1.
 */
typedef struct curve25519_masked_scalar_r {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[kCurve25519MaskedScalarRWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[kCurve25519MaskedScalarRWords];
} curve25519_masked_scalar_r_t;

/**
 * Start an async Ed25519 keygen operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param hash_h_low 32 low bytes of the key hash.
 * @return Result of the operation (OK or error).
 */
status_t curve25519_keygen_start(const curve25519_masked_scalar_s_t *s);

/**
 * Finish an async Ed25519 keygen operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param public_key Pointer for public key A.
 * @return Result of the operation (OK or error).
 */
status_t curve25519_keygen_finalize(uint32_t public_key[kCurve25519PointWords]);

/**
 * Start stage 1 of an async Ed25519 sign operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param r The masked scalar r.
 * @param s The masked scalar s.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_sign_stage1_start(const curve25519_masked_scalar_r_t *r,
                                      const curve25519_masked_scalar_s_t *s);

/**
 * Finish stage 1 of an async Ed25519 sign operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param sig_r Pointer for signature commitment R.
 * @param public_key Pointer for public key A.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_sign_stage1_finalize(
    curve25519_signature_t *sig, uint32_t public_key[kCurve25519PointWords]);

/**
 * Start stage 2 of an async Ed25519 sign operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param hash_k Challenge hash k.
 * @param r The masked scalar r.
 * @param s The masked scalar s.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_sign_stage2_start(
    const uint32_t hash_k[kCurve25519HashWords],
    const curve25519_masked_scalar_r_t *r,
    const curve25519_masked_scalar_s_t *s);

/**
 * Finish stage 2 of an async Ed25519 sign operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param sig_s Pointer for signature response S.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_sign_stage2_finalize(curve25519_signature_t *sig);

/**
 * Start an async Ed25519 verify operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param hash_k Challenge hash k.
 * @param sig_r Signature commitment R.
 * @param sig_s Signature response S.
 * @param public_key Public Key A.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_verify_start(
    const uint32_t hash_k[kCurve25519HashWords], curve25519_signature_t *sig,
    const uint32_t public_key[kCurve25519PointWords]);

/**
 * Finish an async Ed25519 verify operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param result Output buffer (true if signature is valid, false otherwise)
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_verify_finalize(hardened_bool_t *result);

/**
 * Start an async X25519 key exchange operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key The unmasked private key.
 * @param public_key The public key from the other party.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_x25519_start(
    const uint32_t private_key[kCurve25519ScalarWords],
    const uint32_t public_key[kCurve25519PointWords]);

/**
 * Finish an async X25519 key exchange operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param shared_secret Output buffer for the computed shared secret.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_x25519_finalize(
    uint32_t shared_secret[kCurve25519PointWords]);

/**
 * Start an async X25519 keygen operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key The unmasked private key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_x25519_keygen_start(
    const uint32_t private_key[kCurve25519ScalarWords]);

/**
 * Finish an async X25519 keygen operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param public_key Output buffer for the generated public key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_x25519_keygen_finalize(
    uint32_t public_key[kCurve25519PointWords]);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_CURVE25519_H_
