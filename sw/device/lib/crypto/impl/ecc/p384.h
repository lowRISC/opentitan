// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/include/p384.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Start an async P-384 keypair generation operation on OTBN.
 *
 * Appropriate for both ECDSA and ECDH; the key-generation process is the same.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_keygen_start(void);

/**
 * Finish an async P-384 keypair generation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] private_key Generated private key.
 * @param[out] public_key Generated public key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_keygen_finalize(p384_masked_scalar_t *private_key,
                              p384_point_t *public_key);

/**
 * Start an async P-384 sideloaded keypair generation operation on OTBN.
 *
 * Appropriate for both ECDSA and ECDH; the key-generation process is the same.
 *
 * Expects a sideloaded key from keymgr to be already loaded on OTBN. Returns
 * an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_sideload_keygen_start(void);

/**
 * Finish an async P-384 sideloaded keypair generation operation on OTBN.
 *
 * This routine will only read back the public key, instead of both public and
 * private as with `p384_ecdsa_keygen_finalize`. Blocks until OTBN is idle.
 *
 * @param[out] public_key Public key.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_sideload_keygen_finalize(p384_point_t *public_key);

/**
 * Start an async ECDSA/P-384 signature generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @param private_key Secret key to sign the message with.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdsa_sign_start(const uint32_t digest[kP384ScalarWords],
                               p384_masked_scalar_t *private_key);

/**
 * Start an async ECDSA/P-384 signature generation operation on OTBN.
 *
 * This function allows for configuration of the secret scalar k.
 * KATs for FIPS CMVP compliance require ECDSA implementations to receive
 * non-random selected ephemeral k as input (see p.82 bottom in Implementation
 * Guidance for FIPS 140-3 and the Cryptographic Module Validation Program).
 * https://csrc.nist.gov/csrc/media/Projects/cryptographic-module-validation-program/documents/fips%20140-3/FIPS%20140-3%20IG.pdf
 *
 * Note that the provided secret scalar k is not re-blinded before signature
 * generation. This is inline with the strict recommendation that every secret
 * scalar in ECDSA is strictly only ever used once. The scalar is provided as
 * 448b which includes implicit blinding, and in arithmetic shares.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @param private_key Secret key to sign the message with.
 * @param secret_scalar Secret scalar to sign the message with.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdsa_sign_config_k_start(const uint32_t digest[kP384ScalarWords],
                                        p384_masked_scalar_t *private_key,
                                        p384_masked_scalar_t *secret_scalar);

/**
 * Start an async ECDSA/P-384 signature generation operation on OTBN.
 *
 * Expects a sideloaded key from keymgr to be already loaded on OTBN. Returns
 * an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param digest Digest of the message to sign.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdsa_sideload_sign_start(
    const uint32_t digest[kP384ScalarWords]);

/**
 * Finish an async ECDSA/P-384 signature generation operation on OTBN.
 *
 * See the documentation of `p384_ecdsa_sign` for details.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] result Buffer in which to store the generated signature.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdsa_sign_finalize(p384_ecdsa_signature_t *result);

/**
 * Start an async ECDSA/P-384 signature verification operation on OTBN.
 *
 * See the documentation of `p384_ecdsa_verify` for details.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param signature Signature to be verified.
 * @param digest Digest of the message to check the signature against.
 * @param public_key Key to check the signature against.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdsa_verify_start(const p384_ecdsa_signature_t *signature,
                                 const uint32_t digest[kP384ScalarWords],
                                 const p384_point_t *public_key);

/**
 * Finish an async ECDSA/P-384 signature verification operation on OTBN.
 *
 * See the documentation of `p384_ecdsa_verify` for details.
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
status_t p384_ecdsa_verify_finalize(const p384_ecdsa_signature_t *signature,
                                    hardened_bool_t *result);

/**
 * Start an async ECDH/P-384 shared key generation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param private_key Private key (d).
 * @param public_key Public key (Q).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdh_start(p384_masked_scalar_t *private_key,
                         const p384_point_t *public_key);

/**
 * Finish an async ECDH/P-384 shared key generation operation on OTBN.
 *
 * Blocks until OTBN is idle. May be used after either `p384_ecdh_start` or
 * `p384_sideload_ecdh_start`; the operation is the same.
 *
 * @param[out] shared_key Shared secret key (x-coordinate of d*Q).
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_ecdh_finalize(p384_ecdh_shared_key_t *shared_key);

/**
 * Start an async ECDH/P-384 shared key generation operation on OTBN.
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
status_t p384_sideload_ecdh_start(const p384_point_t *public_key);

/**
 * Conduct a point is on curve check operation on OTBN.
 *
 * Checks if the provided point in the affine form is on the P-384 curve.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param point The point to check.
 * @param[out] result True if point is valid, false otherwise.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t p384_point_on_curve_check(const p384_point_t *point,
                                   hardened_bool_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_ECC_P384_H_
