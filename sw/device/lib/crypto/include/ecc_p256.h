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
 * Generates a key pair for ECDSA with curve P-256 using the CDI key.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and use the private key handle
 * returned by `otcrypto_hw_backed_attestation_key`.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @param attestation_seed The additional per-chip fixed entropy.
 * @return Result of the ECDSA key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_dice_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *attestation_seed);

/**
 * Generates an ECDSA signature with curve P-256.
 *
 * The message digest must be exactly 256 bits (32 bytes) long, but may use any
 * hash mode. The caller is responsible for ensuring that the security
 * strength of the hash function is at least equal to the security strength of
 * the curve, but in some cases it may be truncated. See FIPS 186-5 for
 * details.
 *
 * This function should only be used for known answer testing.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param secret_scalar Pointer to the blinded secret scalar (k) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of the ECDSA signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_sign_config_k(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_blinded_key_t *secret_scalar,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t *signature);

/**
 * Generates an ECDSA signature with curve P-256.
 *
 * The message digest must be exactly 256 bits (32 bytes) long, but may use any
 * hash mode. The caller is responsible for ensuring that the security
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
    otcrypto_word32_buf_t *signature);

/**
 * Generates an ECDSA signature with curve P-256 and verifies the signature
 * before releasing it to mitigate fault injection attacks.
 *
 * The message digest must be exactly 256 bits (32 bytes) long, but may use any
 * hash mode. The caller is responsible for ensuring that the security
 * strength of the hash function is at least equal to the security strength of
 * the curve, but in some cases it may be truncated. See FIPS 186-5 for
 * details.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of the ECDSA signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_sign_verify(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_hash_digest_t message_digest,
    otcrypto_word32_buf_t *signature);

/**
 * Verifies an ECDSA/P-256 signature.
 *
 * The message digest must be exactly 256 bits (32 bytes) long, but may use any
 * hash mode. The caller is responsible for ensuring that the security
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
    const otcrypto_const_word32_buf_t *signature,
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
 * Starts asynchronous key generation for P-256 with the CDI key.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and use the private key handle
 * returned by `otcrypto_hw_backed_attestation_key`.
 *
 * @param private_key Destination structure for key handle.
 * @param attestation_seed The additional per-chip fixed entropy.
 * @return Result of asynchronous ECDSA keygen start operation.
 */
otcrypto_status_t otcrypto_ecdsa_p256_dice_keygen_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_word32_buf_t *attestation_seed);

/**
 * Finalizes asynchronous key generation for P-256 with the CDI key.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and use the private key handle
 * returned by `otcrypto_hw_backed_attestation_key`.
 *
 * May block until the operation is complete.
 *
 * The caller should ensure that the private key configuration matches that
 * passed to the `_start` function.
 *
 * @param[out] private_key Key handle, does not return the generated private key
 * (d).
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of asynchronous ECDSA keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_dice_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous signature generation for ECDSA/P-256.
 *
 * This function should only be used for known answer testing.
 *
 * See `otcrypto_ecdsa_p256_sign` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param secret_scalar Pointer to the blinded secret scalar (k) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @return Result of async ECDSA start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_sign_config_k_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_blinded_key_t *secret_scalar,
    const otcrypto_hash_digest_t message_digest);

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
    otcrypto_word32_buf_t *signature);

/**
 * Starts asynchronous signature generation for ECDSA/P-256 with the CDI key.
 *
 * See `otcrypto_ecdsa_p256_sign` for requirements on input values.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and use the private key handle
 * returned by `otcrypto_hw_backed_attestation_key`.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param attestation_seed The additional per-chip fixed entropy.
 * @return Result of async ECDSA start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_dice_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_hash_digest_t message_digest,
    const otcrypto_const_word32_buf_t *attestation_seed);

/**
 * Finalizes asynchronous signature generation for ECDSA/P-256 with the CDI key.
 *
 * See `otcrypto_ecdsa_p256_sign` for requirements on input values.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and use the private key handle
 * returned by `otcrypto_hw_backed_attestation_key`.
 *
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of async ECDSA finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecdsa_p256_dice_sign_async_finalize(
    otcrypto_word32_buf_t *signature);

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
    const otcrypto_const_word32_buf_t *signature);

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
    const otcrypto_const_word32_buf_t *signature,
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

/**
 * Imports an externally-generated P-256 private key from two additive shares.
 *
 * The caller supplies the private key material as two additive shares
 * (share0, share1) over a 320-bit domain (256-bit scalar + 64 redundant bits).
 * The internal key d is defined as:
 *   d = (share0 + share1) mod n
 * where n is the P-256 curve order. The extra 64 bits in each share provide
 * side-channel protection and must be present; callers generating a key from
 * a 256-bit scalar may set the upper 64 bits of one share to zero and the
 * other share to zero entirely (i.e. share1 = 0). The stored representation
 * matches the format produced by `otcrypto_ecdsa_p256_keygen` and
 * `otcrypto_ecdh_p256_keygen`.
 *
 * The caller must allocate and partially populate the blinded key struct
 * before calling this function:
 *   - `config.key_mode` must be `kOtcryptoKeyModeEcdsaP256` or
 *     `kOtcryptoKeyModeEcdhP256`, depending on the intended use.
 *   - `config.key_length` must be 32 bytes (256-bit scalar).
 *   - `keyblob` must point to a caller-allocated 20-word (80-byte) buffer.
 *   - `keyblob_length` must be 80.
 *
 * The `checksum` field of the blinded key struct is populated by this
 * function.
 *
 * @param share0 First share of the private key (must be exactly 10 words /
 *               320 bits).
 * @param share1 Second share of the private key (must be exactly 10 words /
 *               320 bits).
 * @param[out] private_key Blinded private key struct, partially populated by
 *             the caller as described above.
 * @return Result of the P-256 private key import operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecc_p256_private_key_import(
    otcrypto_const_word32_buf_t share0, otcrypto_const_word32_buf_t share1,
    otcrypto_blinded_key_t *private_key);

/**
 * Exports a P-256 private key as two additive shares.
 *
 * Extracts the two 320-bit additive shares from the blinded private key
 * struct. This is the inverse of `otcrypto_ecc_p256_private_key_import`.
 *
 * The private key d is recovered as:
 *   d = (share0 + share1) mod n
 * where n is the P-256 curve order. The shares are returned in the same
 * 320-bit format (256-bit scalar + 64 redundant bits) used internally and
 * produced by `otcrypto_ecdsa_p256_keygen` / `otcrypto_ecdh_p256_keygen`.
 *
 * The caller must allocate and partially populate the output buffers before
 * calling this function:
 *   - `share0->data` and `share1->data` must each point to a caller-allocated
 *     buffer of exactly 10 words (320 bits).
 *   - `share0->len` and `share1->len` must each be set to 10.
 *
 * @param private_key Blinded private key struct to export.
 * @param[out] share0 First share of the private key (must be exactly 10
 *             words / 320 bits).
 * @param[out] share1 Second share of the private key (must be exactly 10
 *             words / 320 bits).
 * @return Result of the P-256 private key export operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecc_p256_private_key_export(
    const otcrypto_blinded_key_t *private_key, otcrypto_word32_buf_t *share0,
    otcrypto_word32_buf_t *share1);

/**
 * Imports an externally-generated P-256 public key from affine coordinates.
 *
 * The caller supplies the uncompressed affine coordinates (x, y) of the
 * public point Q. No on-curve validation is performed here; it is deferred
 * to the point of use (sign, verify, ECDH), consistent with the rest of the
 * P-256 API. If desired, an explicit check if point on curve call can be made
 * to the API.
 *
 * The caller must allocate and partially populate the unblinded key struct
 * before calling this function:
 *   - `key_mode` must be `kOtcryptoKeyModeEcdsaP256` or
 *     `kOtcryptoKeyModeEcdhP256`, depending on the intended use.
 *   - `key_length` must be 64 bytes (two 256-bit coordinates).
 *   - `key` must point to a caller-allocated 16-word (64-byte) buffer.
 *
 * Coordinates are stored as [x || y], each in little-endian word order,
 * matching the layout used by the rest of the P-256 implementation.  The
 * `checksum` field of the unblinded key struct is populated by this function.
 *
 * @param x Affine x-coordinate of the public key (must be exactly 8 words).
 * @param y Affine y-coordinate of the public key (must be exactly 8 words).
 * @param[out] public_key Unblinded public key struct (Q), partially populated
 *             by the caller as described above.
 * @return Result of the P-256 public key import operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecc_p256_public_key_import(
    const otcrypto_const_word32_buf_t x, const otcrypto_const_word32_buf_t y,
    otcrypto_unblinded_key_t *public_key);

/**
 * Exports the affine coordinates of a P-256 public key.
 *
 * Extracts the affine x and y coordinates from the unblinded public key
 * struct. This is the inverse of `otcrypto_ecc_p256_public_key_import`.
 *
 * The caller must allocate and partially populate the output buffers before
 * calling this function:
 *   - `x->data` and `y->data` must each point to a caller-allocated buffer of
 *     exactly 8 words (256 bits).
 *   - `x->len` and `y->len` must each be set to 8.
 *
 * @param public_key Unblinded public key struct (Q) to export.
 * @param[out] x Affine x-coordinate of the public key (must be exactly 8
 *             words).
 * @param[out] y Affine y-coordinate of the public key (must be exactly 8
 *             words).
 * @return Result of the P-256 public key export operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ecc_p256_public_key_export(
    const otcrypto_unblinded_key_t *public_key, otcrypto_word32_buf_t *x,
    otcrypto_word32_buf_t *y);

/**
 * Is on curve check for given P-256 point.
 *
 * @param point Point in the affine coordinates representation that should be
 * checked.
 * @return Result of the point valid check operation.
 */
otcrypto_status_t otcrypto_ecc_p256_point_on_curve(
    const otcrypto_unblinded_key_t *point, hardened_bool_t *check_result);

/**
 * Base point multiplication given a private key.
 *
 * This routine should never be used if the resulting affine coordinates are
 * sensitive values. They are returned unmasked.
 *
 * @param private_key The private key to be multiplied with the base point.
 * @param public_key The resulting public key of the base point multiplication.
 * @return Result of the base point multiplication.
 */
status_t otcrypto_ecc_p256_base_point_mult(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key);

/**
 * Arithmetically share a private key provided as Boolean shares.
 *
 * Given a Boolean-shared 320-bit key d this function arithmetically shares the
 * key such that d = d0 + d1 mod n where n is the curve order.
 *
 * It is allowed to pass the key in plain with the second share being set to 0.
 *
 * Note that no checks are performed to verify whether the input key d is in
 * the interval, this is the responsibility of the caller. I.e., this routine
 * does not (!) provide checks as per FIPS 186-5 for the case of generating a
 * key without extra random bits. The routine will though reduce modulo n
 * implicitly. The routine can be used to generate keys according to FIPS 186-5
 * with extra random bits. The modulo n reduction will not introduce bias due
 * to the extra bits. Note that the routine will not check for zero.
 *
 * @param bool_private_key_share0 First Boolean share of the private key.
 * @param bool_private_key_share1 Second Boolean share of the private key.
 * @param arith_shared_private_key The resulting arithmetically shared key.
 * @return Result of the sharing operation.
 */
otcrypto_status_t otcrypto_ecc_p256_arith_share_private_key(
    const otcrypto_const_word32_buf_t *bool_private_key_share0,
    const otcrypto_const_word32_buf_t *bool_private_key_share1,
    otcrypto_blinded_key_t *arith_private_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_P256_H_
