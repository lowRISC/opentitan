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
 * Generates a key pair for Ed25519.
 *
 * The caller should allocate and partially populate the blinded private key
 * struct, including setting the key configuration (`kOtcryptoKeyModeEd25519`,
 * 32-byte key length, `hw_backed = kHardenedBoolFalse`) and allocating 80
 * bytes for the keyblob. This function pulls a fresh 32-byte Ed25519 seed in
 * two shares from the CSRNG, populates the private key struct and its
 * checksum, and derives the corresponding public key.
 *
 * The caller must also allocate the public key struct and its `key` buffer
 * (32 bytes) before calling this function. The `checksum` field will be
 * populated on success.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the Ed25519 key generation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if key
 * configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen(otcrypto_blinded_key_t *private_key,
                                          otcrypto_unblinded_key_t *public_key);

/**
 * Derives the Ed25519 public key corresponding to a given private key.
 *
 * The private key must be a pre-existing 32-byte Ed25519 seed with a valid
 * checksum (e.g. as returned by `otcrypto_curve25519_private_key_import`). The
 * public key is
 * derived by SHA-512-hashing the seed, clamping the result to obtain the
 * secret scalar, and multiplying the Ed25519 base point by that scalar.
 *
 * The caller must allocate the public key struct and its `key` buffer
 * (32 bytes) before calling this function. The `checksum` field will be
 * populated on success.
 * @param private_key Pointer to the blinded private key struct which is
 * shared into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the Ed25519 key generation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if key
 * configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
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
 * @return Result of the Ed25519 signature generation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments, key configuration, or buffer lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware check fails.
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
 * @return Result of the Ed25519 verification operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or buffer lengths are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result);

/**
 * Checks whether a given encoded point is on the Ed25519 curve.
 *
 * The `point` will be verified whether it is a valid Ed25519 point or not.
 *
 * @param point Key object wrapping the 32-byte encoded Ed25519 point.
 * @param[out] check_result Result of the point on curve check.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_point_on_curve(
    const otcrypto_unblinded_key_t *point, hardened_bool_t *check_result);

/**
 * Generates an Ed25519 signature and verifies the signature
 * before releasing it to mitigate fault injection attacks.
 *
 * The caller must ensure that `private_key` and `public_key` belong to the
 * same Ed25519 keypair. A signature verification failure (including from a
 * mismatched keypair) is treated as a fault and immediately traps the CPU via
 * `HARDENED_CHECK_EQ`. To verify that the keys match beforehand, derive the
 * public key with `otcrypto_ed25519_public_key_from_private_async_start` and
 * `otcrypto_ed25519_public_key_from_private_async_finalize` and compare it
 * against `public_key->key`.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Message digest to be signed.
 * @param sign_mode EdDSA signature hashing mode.
 * @param[out] signature Pointer to the EdDSA signature with (r,s) values.
 * @return Result of the Ed25519 signature generation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments, key configuration, or buffer lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or signature
 * verification check fails.
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
 * Pulls a fresh private key seed in two shares from the CSRNG and starts the
 * OTBN public-key derivation routine. See `otcrypto_ed25519_keygen` for
 * requirements on input values.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @return Result of asynchronous Ed25519 keygen start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if key
 * configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen_async_start(
    otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous key generation for Ed25519.
 *
 * See `otcrypto_ed25519_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param private_key Pointer to the blinded private key struct populated by
 * `otcrypto_ed25519_keygen_async_start`.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous Ed25519 keygen finalize operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments or key
 * length are invalid, or `kOtcryptoStatusValueFatalError` if an internal
 * hardware or integrity check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous public key derivation for Ed25519.
 *
 * See `otcrypto_ed25519_public_key_from_private` for requirements on input
 * values.
 *
 * @param private_key Pointer to the blinded private key struct which is shared
 * into d0, d1 such that d = d0 + d1 mod 2^256.
 * @return Result of asynchronous Ed25519 keygen start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if key
 * configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
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
 * @return Result of asynchronous ed25519 keygen finalize operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments or key
 * length are invalid, or `kOtcryptoStatusValueFatalError` if an internal
 * hardware or integrity check fails.
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
 * @return Result of async Ed25519 start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments, key configuration, or buffer lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
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
 * @param[out] signature Pointer to the EdDSA signature to get (R) value.
 * @param s0 Pointer to the first arithmetic share of s.
 * @param s1 Pointer to the second arithmetic share of s.
 * @param r0 Pointer to the first arithmetic share of r.
 * @param r1 Pointer to the second arithmetic share of r.
 * @return Result of async Ed25519 start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments, key
 * configuration, or buffer lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
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
 * @return Result of async Ed25519 finalize operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments or
 * signature buffer length are invalid, or `kOtcryptoStatusValueFatalError` if
 * an internal hardware or integrity check fails.
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
 * @return Result of async Ed25519 verification start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or buffer lengths are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware or integrity check fails.
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
 * @return Result of async Ed25519 verification finalize operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware or
 * integrity check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result);

/**
 * Generates a key pair for X25519.
 *
 * The caller should allocate and partially populate the blinded private key
 * struct, including populating the key configuration and allocating space for
 * the keyblob. For a hardware-backed key, use the private key handle returned
 * by `otcrypto_hw_backed_key`. Otherwise, the mode should indicate X25519
 * (`kOtcryptoKeyModeX25519`) and the keyblob should be 80 bytes; this function
 * pulls a fresh 32-byte private key in two shares from the CSRNG, populates
 * the private key struct and its checksum, and derives the corresponding
 * public key.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the X25519 key generation. Returns `kOtcryptoStatusValueOk`
 * on success, `kOtcryptoStatusValueBadArgs` if key configuration or keyblob
 * length is invalid, or `kOtcryptoStatusValueFatalError` if an internal
 * hardware or integrity check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen(otcrypto_blinded_key_t *private_key,
                                         otcrypto_unblinded_key_t *public_key);

/**
 * Derives an X25519 public key from a given private key.
 *
 * The private key must be a pre-existing 32-byte X25519 seed (or sideloaded
 * hardware key) with a valid checksum. The public key is derived by clamping
 * the private key according to RFC 7748 and multiplying it by the X25519 base
 * point.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the X25519 public key derivation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if key
 * configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_public_key_from_private(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key);

/**
 * Performs X25519 key exchange.
 *
 * Computes a shared secret by multiplying the provided public key from the
 * other party by the caller's private key.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param public_key Pointer to the unblinded public key struct from the other
 * party.
 * @param[out] shared_secret Pointer to the blinded shared secret struct
 *                           (must use a symmetric key mode).
 * @return Result of the X25519 key exchange. Returns `kOtcryptoStatusValueOk`
 * on success, `kOtcryptoStatusValueBadArgs` if arguments, key configuration, or
 * buffer lengths are invalid, or `kOtcryptoStatusValueFatalError` if an
 * internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519(const otcrypto_blinded_key_t *private_key,
                                  const otcrypto_unblinded_key_t *public_key,
                                  otcrypto_blinded_key_t *shared_secret);

/**
 * Starts asynchronous key generation for X25519.
 *
 * Pulls a fresh private key in two shares from the CSRNG (when software-backed)
 * and starts the OTBN public-key derivation routine. See
 * `otcrypto_x25519_keygen` for requirements on input values.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @return Result of asynchronous X25519 keygen start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if key
 * configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen_async_start(
    otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous key generation for X25519.
 *
 * See `otcrypto_x25519_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous X25519 keygen finalize operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments or key
 * lengths are invalid, or `kOtcryptoStatusValueFatalError` if an internal
 * hardware or integrity check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous public key derivation for X25519.
 *
 * See `otcrypto_x25519_public_key_from_private` for requirements on input
 * values.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @return Result of asynchronous X25519 public key derivation start operation.
 * Returns `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * key configuration or keyblob length is invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_public_key_from_private_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes asynchronous public key derivation for X25519.
 *
 * See `otcrypto_x25519_public_key_from_private` for requirements on input
 * values.
 *
 * May block until the operation is complete.
 *
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous X25519 public key derivation finalize
 * operation. Returns `kOtcryptoStatusValueOk` on success,
 * `kOtcryptoStatusValueAsyncIncomplete` if OTBN is still processing,
 * `kOtcryptoStatusValueBadArgs` if arguments or key lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_public_key_from_private_async_finalize(
    otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous X25519 key exchange.
 *
 * See `otcrypto_x25519` for requirements on input values.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous X25519 start operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments, key configuration, or buffer lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key);

/**
 * Finalizes asynchronous X25519 key exchange.
 *
 * See `otcrypto_x25519` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] shared_secret Pointer to the blinded shared secret struct
 *                           (must use a symmetric key mode).
 * @return Result of asynchronous X25519 finalize operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueAsyncIncomplete` if
 * OTBN is still processing, `kOtcryptoStatusValueBadArgs` if arguments, key
 * configuration, or buffer lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal hardware or integrity check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_async_finalize(
    otcrypto_blinded_key_t *shared_secret);

/**
 * Imports an externally-generated Curve25519 private key from two additive
 * shares.
 *
 * The caller supplies the private key material (a 32-byte RFC 8032 seed for
 * Ed25519 or a 32-byte scalar for X25519) as two 320-bit (10-word) additive
 * shares (`share0`, `share1`). Curve25519 uses the lower 256 bits (8 words):
 *   d = (share0 + share1) mod 2^256
 * while the upper 64 bits (2 words) per share match the ECC keyblob layout and
 * are ignored by Curve25519 operations. Callers importing from an unmasked
 * 256-bit value may set the upper 2 words to zero and split via `hardened_sub`
 * (or set `share1` to all-zero words).
 *
 * The caller must allocate and partially populate the blinded key struct
 * before calling this function:
 *   - `config.key_mode` must be `kOtcryptoKeyModeEd25519` or
 *     `kOtcryptoKeyModeX25519`.
 *   - `config.key_length` must be 32 bytes.
 *   - `config.hw_backed` must be `kHardenedBoolFalse`.
 *   - `keyblob` must point to a caller-allocated 20-word (80-byte) buffer (or
 *     10-word / 40-byte buffer when `OTCRYPTO_DISABLE_KEYBLOB_MASKING` is
 *     enabled), and `keyblob_length` must match.
 *
 * The `checksum` field of the blinded key struct is populated by this
 * function.
 *
 * @param share0 First share of the private key (must be 10 words / 320 bits).
 * @param share1 Second share of the private key (must be 10 words / 320 bits).
 * @param[out] private_key Blinded private key struct, partially populated by
 *             the caller as described above.
 * @return Result of the Curve25519 private key import operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments, key configuration, or share lengths are invalid, or
 * `kOtcryptoStatusValueFatalError` if an internal integrity check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_curve25519_private_key_import(
    otcrypto_const_word32_buf_t share0, otcrypto_const_word32_buf_t share1,
    otcrypto_blinded_key_t *private_key);

/**
 * Exports a Curve25519 private key as two additive shares.
 *
 * Extracts the two 320-bit (10-word) additive shares (`share0`, `share1`) from
 * the blinded private key struct, where the 256-bit key material is recovered
 * from the lower 8 words as:
 *   d = (share0 + share1) mod 2^256
 * This is the inverse of `otcrypto_curve25519_private_key_import`.
 *
 * Hardware-backed keys and keys without `config.exportable` set to
 * `kHardenedBoolTrue` cannot be exported and will return
 * `kOtcryptoStatusValueBadArgs`.
 *
 * @param private_key Blinded private key struct (`kOtcryptoKeyModeEd25519` or
 *                    `kOtcryptoKeyModeX25519`) to export.
 * @param[out] share0 Buffer to receive the first 10-word (320-bit) share.
 * @param[out] share1 Buffer to receive the second 10-word (320-bit) share.
 * @return Result of the Curve25519 private key export operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments, key configuration, exportability, integrity checksum, or share
 * lengths are invalid, or `kOtcryptoStatusValueFatalError` if an internal
 * check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_curve25519_private_key_export(
    const otcrypto_blinded_key_t *private_key, otcrypto_word32_buf_t *share0,
    otcrypto_word32_buf_t *share1);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_CURVE25519_H_
