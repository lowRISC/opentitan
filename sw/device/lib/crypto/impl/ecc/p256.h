// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P256_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Length of a P-256 curve point coordinate in bits (modulo p).
   */
  kP256CoordBits = 256,
  /**
   * Length of a P-256 curve point coordinate in bytes.
   */
  kP256CoordBytes = kP256CoordBits / 8,
  /**
   * Length of a P-256 curve point coordinate in words.
   */
  kP256CoordWords = kP256CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the P-256 scalar field (modulo the curve order n).
   */
  kP256ScalarBits = 256,
  /**
   * Length of a secret scalar share in bytes.
   */
  kP256ScalarBytes = kP256ScalarBits / 8,
  /**
   * Length of secret scalar share in words.
   */
  kP256ScalarWords = kP256ScalarBytes / sizeof(uint32_t),
  /**
   * Length of a masked secret scalar share.
   *
   * This implementation uses extra redundant bits for side-channel protection.
   */
  kP256MaskedScalarShareBits = kP256ScalarBits + 64,
  /**
   * Length of a masked secret scalar share in bytes.
   */
  kP256MaskedScalarShareBytes = kP256MaskedScalarShareBits / 8,
  /**
   * Length of masked secret scalar share in words.
   */
  kP256MaskedScalarShareWords = kP256MaskedScalarShareBytes / sizeof(uint32_t),
};

/**
 * A type that holds a masked value from the P-256 scalar field.
 *
 * This struct is used to represent secret keys, which are integers modulo n.
 * The key d is represented in two 320-bit shares, d0 and d1, such that d = (d0
 * + d1) mod n. Mathematically, d0 and d1 could also be reduced modulo n, but
 * the extra bits provide side-channel protection.
 */
typedef struct p256_masked_scalar {
  /**
   * First share of the secret scalar.
   */
  uint32_t share0[kP256MaskedScalarShareWords];
  /**
   * Second share of the secret scalar.
   */
  uint32_t share1[kP256MaskedScalarShareWords];
} p256_masked_scalar_t;

/**
 * A type that holds a P-256 curve point.
 */
typedef struct p256_point {
  /**
   * Affine x-coordinate.
   */
  uint32_t x[kP256CoordWords];
  /**
   * Affine y-coordinate.
   */
  uint32_t y[kP256CoordWords];
} p256_point_t;

/**
 * A type that holds an ECDSA/P-256 signature.
 *
 * The signature consists of two integers r and s, computed modulo n.
 */
typedef struct p256_ecdsa_signature_t {
  uint32_t r[kP256ScalarWords];
  uint32_t s[kP256ScalarWords];
} p256_ecdsa_signature_t;

/**
 * A type that holds a blinded ECDH shared secret key.
 *
 * The key is boolean-masked (XOR of the two shares).
 */
typedef struct p256_ecdh_shared_key {
  uint32_t share0[kP256CoordWords];
  uint32_t share1[kP256CoordWords];
} p256_ecdh_shared_key_t;

/**
 * Start an async P-256 keypair generation operation on OTBN.
 *
 * Appropriate for both ECDSA and ECDH; the key-generation process is the same.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_keygen_start(void);

/**
 * Finish an async P-256 keypair generation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] private_key Generated private key.
 * @param[out] public_key Generated public key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_keygen_finalize(p256_masked_scalar_t *private_key,
                              p256_point_t *public_key);

/**
 * Start an async P-256 sideloaded keypair generation operation on OTBN.
 *
 * Appropriate for both ECDSA and ECDH; the key-generation process is the same.
 *
 * Expects a sideloaded key from keymgr to be already loaded on OTBN. Returns
 * an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_sideload_keygen_start(void);

/**
 * Finish an async P-256 sideloaded keypair generation operation on OTBN.
 *
 * This routine will only read back the public key, instead of both public and
 * private as with `p256_ecdsa_keygen_finalize`. Blocks until OTBN is idle.
 *
 * @param[out] public_key Public key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_sideload_keygen_finalize(p256_point_t *public_key);

/**
 * Start an async ECDSA/P-256 signature generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @param private_key Secret key to sign the message with.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdsa_sign_start(const uint32_t digest[kP256ScalarWords],
                               const p256_masked_scalar_t *private_key);

/**
 * Start an async ECDSA/P-256 signature generation operation on OTBN.
 *
 * Expects a sideloaded key from keymgr to be already loaded on OTBN. Returns
 * an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdsa_sideload_sign_start(
    const uint32_t digest[kP256ScalarWords]);

/**
 * Finish an async ECDSA/P-256 signature generation operation on OTBN.
 *
 * See the documentation of `p256_ecdsa_sign` for details.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] result Buffer in which to store the generated signature.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdsa_sign_finalize(p256_ecdsa_signature_t *result);

/**
 * Start an async ECDSA/P-256 signature verification operation on OTBN.
 *
 * See the documentation of `p256_ecdsa_verify` for details.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param signature Signature to be verified.
 * @param digest Digest of the message to check the signature against.
 * @param public_key Key to check the signature against.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdsa_verify_start(const p256_ecdsa_signature_t *signature,
                                 const uint32_t digest[kP256ScalarWords],
                                 const p256_point_t *public_key);

/**
 * Finish an async ECDSA/P-256 signature verification operation on OTBN.
 *
 * See the documentation of `p256_ecdsa_verify` for details.
 *
 * Blocks until OTBN is idle.
 *
 * If the signature is valid, writes `kHardenedBoolTrue` to `result`;
 * otherwise, writes `kHardenedBoolFalse`.
 *
 * Note: the caller must check the `result` buffer in order to determine if a
 * signature passed verification. If a signature is invalid, but nothing goes
 * wrong during computation (e.g. hardware errors, failed preconditions), the
 * status will be OK but `result` will be `kHardenedBoolFalse`.
 *
 * @param signature Signature to be verified.
 * @param[out] result Output buffer (true if signature is valid, false
 * otherwise)
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdsa_verify_finalize(const p256_ecdsa_signature_t *signature,
                                    hardened_bool_t *result);

/**
 * Start an async ECDH/P-256 shared key generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key Private key (d).
 * @param public_key Public key (Q).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdh_start(const p256_masked_scalar_t *private_key,
                         const p256_point_t *public_key);

/**
 * Finish an async ECDH/P-256 shared key generation operation on OTBN.
 *
 * Blocks until OTBN is idle. May be used after either `p256_ecdh_start` or
 * `p256_sideload_ecdh_start`; the operation is the same.
 *
 * @param[out] shared_key Shared secret key (x-coordinate of d*Q).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_ecdh_finalize(p256_ecdh_shared_key_t *shared_key);

/**
 * Start an async ECDH/P-256 shared key generation operation on OTBN.
 *
 * Uses a private key generated from a key manager seed. The key manager should
 * already have sideloaded the key into OTBN before this operation is called.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key Public key (Q).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p256_sideload_ecdh_start(const p256_point_t *public_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P256_H_
