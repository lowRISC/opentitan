// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_P256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_P256_H_

#include "datatypes.h"

/**
 * @file
 * @brief P-256 elliptic curve operations for OpenTitan cryptography library.
 *
 * Includes ECDSA and ECDH.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Generates a key pair for ECDSA with curve P-256.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. For a hardware-backed key, use the private key handle returned by
 * `otcrypto_hw_backed_key`. Otherwise, the mode should indicate ECDSA with
 * P-256 and the keyblob should be 80 bytes. The value in the `checksum` field
 * of the blinded key struct will be populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of the ECDSA key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Generates an ECDSA signature with curve P-256.
 *
 * The message digest must be exactly 256 bits (32 bytes) long, but may use any
 * hash mode.  The caller is responsible for ensuring that the security
 * strength of the hash function is at least equal to the security strength of
 * the curve, but in some cases it may be truncated. See FIPS 186-5 for
 * details.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of the ECDSA signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t signature);

/**
 * Verifies an ECDSA/P-256 signature.
 *
 * The message digest must be exactly 256 bits (32 bytes) long, but may use any
 * hash mode.  The caller is responsible for ensuring that the security
 * strength of the hash function is at least equal to the security strength of
 * the curve, but in some cases it may be truncated. See FIPS 186-5 for
 * details.
 *
 * The caller must check the `verification_result` parameter, NOT only the
 * returned status code, to know if the signature passed verification. The
 * status code, as for other operations, only indicates whether errors were
 * encountered, and may return OK even when the signature is invalid.
 *
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param message_digest Message digest to be verified (pre-hashed).
 * @param signature Pointer to the signature to be verified.
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of the ECDSA verification operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result);

/**
 * Generates a key pair for ECDH with curve P-256.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. For a hardware-backed key, use the private key handle returned by
 * `otcrypto_hw_backed_key`. Otherwise, the mode should indicate ECDH with
 * P-256 and the keyblob should be 80 bytes. The value in the `checksum` field
 * of the blinded key struct will be populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of the ECDH key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdh_p256_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Elliptic Curve Diffie Hellman shared secret generation with curve P-256.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param[out] shared_secret Pointer to generated blinded shared key struct.
 * @return Result of ECDH shared secret generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdh_p256(const otcrypto_blinded_key_t *private_key,
                                     const otcrypto_unblinded_key_t *public_key,
                                     otcrypto_blinded_key_t *shared_secret);

/**
 * Starts asynchronous key generation for ECDSA/P-256.
 *
 * See `otcrypto_ecdsa_p256_keygen` for requirements on input values.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous ECDSA keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_keygen_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous key generation for ECDSA/P-256.
 *
 * See `otcrypto_ecdsa_p256_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * The caller should ensure that the private key configuration matches that
 * passed to the `_start` function.
 *
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of asynchronous ECDSA keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous signature generation for ECDSA/P-256.
 *
 * See `otcrypto_ecdsa_p256_sign` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @return Result of async ECDSA start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest);

/**
 * Finalizes asynchronous signature generation for ECDSA/P-256.
 *
 * See `otcrypto_ecdsa_p256_sign` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of async ECDSA finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_sign_async_finalize(
    otcrypto_word32_buf_t signature);

/**
 * Starts asynchronous signature verification for ECDSA/P-256.
 *
 * See `otcrypto_ecdsa_p256_verify` for requirements on input values.
 *
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param message_digest Message digest to be verified (pre-hashed).
 * @param signature Pointer to the signature to be verified.
 * @return Result of async ECDSA verify start function.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_const_word32_buf_t signature);

/**
 * Finalizes asynchronous signature verification for ECDSA/P-256.
 *
 * See `otcrypto_ecdsa_p256_verify` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * The caller must check the `verification_result` parameter, NOT only the
 * returned status code, to know if the signature passed verification. The
 * status code, as for other operations, only indicates whether errors were
 * encountered, and may return OK even when the signature is invalid.
 *
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of async ECDSA verify finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_verify_async_finalize(
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result);

/**
 * Starts asynchronous key generation for ECDH/P-256.
 *
 * See `otcrypto_ecdh_p256_keygen` for requirements on input values.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous ECDH keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdh_p256_keygen_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous key generation for ECDH/P-256.
 *
 * See `otcrypto_ecdh_p256_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * The caller should ensure that the private key configuration matches that
 * passed to the `_start` function.
 *
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of asynchronous ECDH keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdh_p256_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous shared secret generation for ECDH/P-256.
 *
 * See `otcrypto_ecdh_p256` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of async ECDH start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdh_p256_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key);

/**
 * Finalizes asynchronous shared secret generation for ECDH/P-256.
 *
 * See `otcrypto_ecdh_p256` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] shared_secret Pointer to generated blinded shared key struct.
 * @return Result of async ECDH finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdh_p256_async_finalize(
    otcrypto_blinded_key_t *shared_secret);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_P256_H_
