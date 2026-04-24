// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_CURVE25519_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_CURVE25519_H_

#include "datatypes.h"

/**
 * @file
 * @brief Ed25519 operations for OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Hashing mode for EdDSA signatures.
 *
 * Values are hardened.
 */
typedef enum otcrypto_eddsa_sign_mode {
  // Signature mode EdDSA.
  kOtcryptoEddsaSignModeEddsa = 0xae1,
  // Signature mode Hashed EdDSA.
  kOtcryptoEddsaSignModeHashEddsa = 0x9a6,
} otcrypto_eddsa_sign_mode_t;

/**
 * Derives the Ed25519 public key corresponding to a given private key.
 *
 * The private key must be a pre-existing 32-byte Ed25519 seed with a valid
 * checksum (e.g. as returned by an import function). The public key is
 * derived by SHA-512-hashing the seed, clamping the result to obtain the
 * secret scalar, and multiplying the Ed25519 base point by that scalar.
 *
 * The caller must allocate the public key struct and its `key` buffer
 * (32 bytes) before calling this function. The `checksum` field will be
 * populated on success.
 * @param private_key Pointer to the blinded private key struct which is
 * shared into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the Ed25519 key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_public_key_from_private(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key);

/**
 * Generates an Ed25519 digital signature.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param input_message Input message to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param[out] signature Pointer to the EdDSA signature with (r,s) values.
 * @return Result of the Ed25519 signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature);

/**
 * Verifies an Ed25519 signature.
 *
 * The caller must check the `verification_result` parameter, NOT only the
 * returned status code, to know if the signature passed verification. The
 * status code, as for other operations, only indicates whether errors were
 * encountered, and may return OK even when the signature is invalid.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Input message to be signed for verification.
 * @param sign_mode EdDSA signature hashing mode.
 * @param signature Pointer to the signature to be verified.
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of the Ed25519 verification operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result);

/**
 * Generates an Ed25519 signature and verifies the signature
 * before releasing it to mitigate fault injection attacks.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Message digest to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param[out] signature Pointer to the EdDSA signature with (r,s) values.
 * @return Result of the Ed25519 signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_verify(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature);

/**
 * Starts asynchronous key generation for Ed25519.
 *
 * See `otcrypto_ed25519_public_key_from_private` for requirements on input
 * values.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @return Result of asynchronous Ed25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_public_key_from_private_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous key generation for Ed25519.
 *
 * See `otcrypto_ed25519_public_key_from_private` for requirements on input
 * values.
 *
 * May block until the operation is complete.
 *
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous ed25519 keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_public_key_from_private_async_finalize(
    otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous signature generation for Ed25519.
 *
 * See `otcrypto_ed25519_sign` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param input_message_ph Pre-hashed input message to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param[out] s0 Pointer to the first arithmetic share of s.
 * @param[out] s1 Pointer to the second arithmetic share of s.
 * @param[out] r0 Pointer to the first arithmetic share of r.
 * @param[out] r1 Pointer to the second arithmetic share of r.
 * @param msg_digest[out] Pointer to the msg digest.
 * @return Result of async Ed25519 start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_part1_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *input_message_ph,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *s0,
    otcrypto_word32_buf_t *s1, otcrypto_word32_buf_t *r0,
    otcrypto_word32_buf_t *r1);

/**
 * Starts asynchronous signature generation for Ed25519.
 *
 * See `otcrypto_ed25519_sign` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param input_message_ph Pre-hashed input message to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param signature[out] Pointer to the EdDSA signature to get (R) value.
 * @param s0 Pointer to the first arithmetic share of s.
 * @param s1 Pointer to the second arithmetic share of s.
 * @param r0 Pointer to the first arithmetic share of r.
 * @param r1 Pointer to the second arithmetic share of r.
 * @return Result of async Ed25519 start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_part2_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *input_message_ph,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t *signature,
    otcrypto_word32_buf_t *s0, otcrypto_word32_buf_t *s1,
    otcrypto_word32_buf_t *r0, otcrypto_word32_buf_t *r1);

/**
 * Finalizes asynchronous signature generation for Ed25519.
 *
 * See `otcrypto_ed25519_sign` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[inout] signature Pointer to the EdDSA signature containing (R) to get
 * (s) value.
 * @return Result of async Ed25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t *signature);

/**
 * Starts asynchronous signature verification for Ed25519.
 *
 * See `otcrypto_ed25519_verify` for requirements on input values.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message_ph Pre-hashed input message to be signed for
 * verification.
 * @param sign_mode EdDSA signature hashing mode.
 * @param signature Pointer to the signature to be verified.
 * @return Result of async Ed25519 verification start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message_ph,
    otcrypto_eddsa_sign_mode_t sign_mode,
    const otcrypto_const_word32_buf_t *signature);

/**
 * Finalizes asynchronous signature verification for Ed25519.
 *
 * See `otcrypto_ed25519_verify` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * The caller must check the `verification_result` parameter, NOT only the
 * returned status code, to know if the signature passed verification. The
 * status code, as for other operations, only indicates whether errors were
 * encountered, and may return OK even when the signature is invalid.
 *
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of async Ed25519 verification finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_CURVE25519_H_
