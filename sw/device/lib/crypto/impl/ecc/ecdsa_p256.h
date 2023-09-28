// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P256_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A type that holds an ECDSA/P-256 signature.
 *
 * The signature consists of two integers r and s, computed modulo n.
 */
typedef struct ecdsa_p256_signature_t {
  uint32_t r[kP256ScalarWords];
  uint32_t s[kP256ScalarWords];
} ecdsa_p256_signature_t;

/**
 * Start an async ECDSA/P-256 keypair generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_keygen_start(void);

/**
 * Start an async ECDSA/P-256 sideloaded keypair generation operation on OTBN.
 *
 * Expects a sideloaded key from keymgr to be already loaded on OTBN. Returns
 * an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_sideload_keygen_start(void);

/**
 * Finish an async ECDSA/P-256 keypair generation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] private_key Generated private key.
 * @param[out] public_key Generated public key.
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_keygen_finalize(p256_masked_scalar_t *private_key,
                                    p256_point_t *public_key);

/**
 * Start an async ECDSA/P-256 sideloaded keypair generation operation on OTBN.
 *
 * This routine will only read back the public key, instead of both public and
 * private as with `ecdsa_p256_keygen_finalize`. Blocks until OTBN is idle.
 *
 * @param[out] public_key Public key.
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_sideload_keygen_finalize(p256_point_t *public_key);

/**
 * Start an async ECDSA/P-256 signature generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @param private_key Secret key to sign the message with.
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_sign_start(const uint32_t digest[kP256ScalarWords],
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
status_t ecdsa_p256_sideload_sign_start(
    const uint32_t digest[kP256ScalarWords]);

/**
 * Finish an async ECDSA/P-256 signature generation operation on OTBN.
 *
 * See the documentation of `ecdsa_p256_sign` for details.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] result Buffer in which to store the generated signature.
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_sign_finalize(ecdsa_p256_signature_t *result);

/**
 * Start an async ECDSA/P-256 signature verification operation on OTBN.
 *
 * See the documentation of `ecdsa_p256_verify` for details.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param signature Signature to be verified.
 * @param digest Digest of the message to check the signature against.
 * @param public_key Key to check the signature against.
 * @return Result of the operation (OK or error).
 */
status_t ecdsa_p256_verify_start(const ecdsa_p256_signature_t *signature,
                                 const uint32_t digest[kP256ScalarWords],
                                 const p256_point_t *public_key);

/**
 * Finish an async ECDSA/P-256 signature verification operation on OTBN.
 *
 * See the documentation of `ecdsa_p256_verify` for details.
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
status_t ecdsa_p256_verify_finalize(const ecdsa_p256_signature_t *signature,
                                    hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_ECDSA_P256_H_
