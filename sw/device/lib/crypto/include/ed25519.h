// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ED25519_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ED25519_H_

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
 * Generates a key pair for Ed25519.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. For a hardware-backed key, use the private key handle returned by
 * `otcrypto_hw_backed_key`. Otherwise, the mode should indicate Ed25519 and the
 * keyblob should be 80 bytes. The value in the `checksum` field of the blinded
 * key struct will be populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the Ed25519 key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen(otcrypto_blinded_key_t *private_key,
                                          otcrypto_unblinded_key_t *public_key);

/**
 * Generates an Ed25519 digital signature.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param input_message Input message to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param[out] signature Pointer to the EdDSA signature with (r,s) values.
 * @return Result of the Ed25519 signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature);

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
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result);

/**
 * Starts asynchronous key generation for Ed25519.
 *
 * See `otcrypto_ed25519_keygen` for requirements on input values.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous Ed25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous key generation for Ed25519.
 *
 * See `otcrypto_ed25519_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * The caller should ensure that the private key configuration matches that
 * passed to the `_start` function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous ed25519 keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous signature generation for Ed25519.
 *
 * See `otcrypto_ed25519_sign` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param input_message Input message to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param[out] signature Pointer to the EdDSA signature to get (r) value.
 * @return Result of async Ed25519 start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature);

/**
 * Finalizes asynchronous signature generation for Ed25519.
 *
 * See `otcrypto_ecdsa_p256_sign` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] signature Pointer to the EdDSA signature to get (s) value.
 * @return Result of async Ed25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t signature);

/**
 * Starts asynchronous signature verification for Ed25519.
 *
 * See `otcrypto_ecdsa_p256_verify` for requirements on input values.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Input message to be signed for verification.
 * @param sign_mode EdDSA signature hashing mode.
 * @param signature Pointer to the signature to be verified.
 * @return Result of async Ed25519 verification start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    otcrypto_const_word32_buf_t signature);

/**
 * Finalizes asynchronous signature verification for Ed25519.
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
 * @return Result of async Ed25519 verification finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ED25519_H_
