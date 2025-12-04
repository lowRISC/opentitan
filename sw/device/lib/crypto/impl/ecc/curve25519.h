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
   * Magic value for verify success response.
   */
  kCurve25519VerifySuccess = 0xf77fe650,
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
 * Start stage 1 of an async Ed25519 sign operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param hash_r Message hash r.
 * @param hash_h_low 32 low bytes of the key hash.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_sign_stage1_start(
    const uint32_t hash_r[kCurve25519HashWords],
    const uint32_t hash_h_low[kCurve25519HalfHashWords]);

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
 * @param hash_r Message hash r.
 * @param hash_h_low 32 low bytes of the key hash.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t curve25519_sign_stage2_start(
    const uint32_t hash_k[kCurve25519HashWords],
    const uint32_t hash_r[kCurve25519HashWords],
    const uint32_t hash_h_low[kCurve25519HalfHashWords]);

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

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_CURVE25519_H_
