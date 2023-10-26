// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_H_

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * @file
 * @brief Elliptic curve operations for OpenTitan cryptography library.
 *
 * Includes ECDSA, ECDH, Ed25519, and X25519.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define EdDSA mode for signature.
 *
 * Values are hardened.
 */
typedef enum eddsa_sign_mode {
  // Signature mode EdDSA.
  kEddsaSignModeEdDSA = 0xae1,
  // Signature mode Hashed EdDSA.
  kEddsaSignModeHashEdDSA = 0x9a6,
} eddsa_sign_mode_t;

/**
 * Struct for domain parameters of a custom Weierstrass curve.
 */
typedef struct ecc_domain {
  // Prime P (modulus of coordinate finite field).
  crypto_const_byte_buf_t p;
  // Coefficient a.
  crypto_const_byte_buf_t a;
  // Coefficient b.
  crypto_const_byte_buf_t b;
  // q (order of G).
  crypto_const_byte_buf_t q;
  // Value of x coordinate of G (basepoint). Same length as p.
  const uint32_t *gx;
  // Value of y coordinate of G (basepoint). Same length as p.
  const uint32_t *gy;
  // Cofactor of the curve.
  const uint32_t cofactor;
  // Checksum value of the parameters.
  uint32_t checksum;
} ecc_domain_t;

/**
 * Enum to define the type of elliptic curve used for the operation.
 *
 * Values are hardened.
 */
typedef enum ecc_curve_type {
  // Generic Weierstrass curve, with custom domain parameters.
  kEccCurveTypeCustom = 0xbf7,
  // Named Weierstrass curve - NIST P256.
  kEccCurveTypeNistP256 = 0xec8,
  // Named Weierstrass curve - NIST P384.
  kEccCurveTypeNistP384 = 0x1bc,
  // Named Weierstrass curve - Brainpool P256r1.
  kEccCurveTypeBrainpoolP256R1 = 0xc1e,
} ecc_curve_type_t;

/**
 * Struct for ECC curve used for ECDSA / ECDH operation.
 *
 * Values are hardened.
 */
typedef struct ecc_curve {
  // Type of the Weierstrass curve, custom curve or named curve.
  ecc_curve_type_t curve_type;
  // Domain parameters for a custom Weierstrass curve. May be NULL for a named
  // curve.
  const ecc_domain_t *const domain_parameter;
} ecc_curve_t;

/**
 * Performs the key generation for ECDSA operation.
 *
 * Computes private key (d) and public key (Q) keys for ECDSA operation.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. For hardware-backed keys, the keyblob length is 0 and the
 * keyblob pointer may be `NULL`. For non-hardware-backed keys, the keyblob
 * should be twice the length of the key. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required only for a
 * custom curve. For named curves this field is ignored and can be set to
 * `NULL`.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of the ECDSA key generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_keygen(const ecc_curve_t *elliptic_curve,
                                      crypto_blinded_key_t *private_key,
                                      crypto_unblinded_key_t *public_key);

/**
 * Performs the ECDSA digital signature generation.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to `NULL`.
 *
 * The message digest must be exactly the right length for the curve in use
 * (e.g. 256 bits for P-256), but may use any hash mode. The caller is
 * responsible for ensuring that the security strength of the hash function is
 * at least equal to the security strength of the curve. See FIPS 186-5 for
 * details.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of the ECDSA signature generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_sign(const crypto_blinded_key_t *private_key,
                                    const hash_digest_t *message_digest,
                                    const ecc_curve_t *elliptic_curve,
                                    crypto_word32_buf_t signature);

/**
 * Performs the ECDSA digital signature verification.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to `NULL`.
 *
 * The message digest must be exactly the right length for the curve in use
 * (e.g. 256 bits for P-256), but may use any hash mode. The caller is
 * responsible for ensuring that the security strength of the hash function is
 * at least equal to the security strength of the curve. See FIPS 186-5 for
 * details.
 *
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param message_digest Message digest to be verified (pre-hashed).
 * @param signature Pointer to the signature to be verified.
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param[out] verification_result Result of signature verification
 * (Pass/Fail).
 * @return Result of the ECDSA verification operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_verify(const crypto_unblinded_key_t *public_key,
                                      const hash_digest_t *message_digest,
                                      crypto_const_word32_buf_t signature,
                                      const ecc_curve_t *elliptic_curve,
                                      hardened_bool_t *verification_result);

/**
 * Performs the key generation for ECDH key agreement.
 *
 * Computes private key (d) and public key (Q) keys for ECDSA operation.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required only for a
 * custom curve. For named curves this field is ignored and can be set to
 * `NULL`.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. For hardware-backed keys, the keyblob length is 0 and the
 * keyblob pointer may be `NULL`. For non-hardware-backed keys, the keyblob
 * should be twice the length of the key. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of the ECDH key generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdh_keygen(const ecc_curve_t *elliptic_curve,
                                     crypto_blinded_key_t *private_key,
                                     crypto_unblinded_key_t *public_key);

/**
 * Performs Elliptic Curve Diffie Hellman shared secret generation.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to `NULL`.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param[out] shared_secret Pointer to generated blinded shared key struct.
 * @return Result of ECDH shared secret generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdh(const crypto_blinded_key_t *private_key,
                              const crypto_unblinded_key_t *public_key,
                              const ecc_curve_t *elliptic_curve,
                              crypto_blinded_key_t *shared_secret);

/**
 * Generates a new Ed25519 key pair.
 *
 * Computes the private exponent (d) and public key (Q) based on
 * Curve25519.
 *
 * No `domain_parameter` is needed and is automatically set for Ed25519.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. For hardware-backed keys, the keyblob length is 0 and the
 * keyblob pointer may be `NULL`. For non-hardware-backed keys, the keyblob
 * should be twice the length of the key. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the Ed25519 key generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_keygen(crypto_blinded_key_t *private_key,
                                        crypto_unblinded_key_t *public_key);

/**
 * Generates an Ed25519 digital signature.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param input_message Input message to be signed.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param[out] signature Pointer to the EdDSA signature with (r,s) values.
 * @return Result of the EdDSA signature generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_sign(const crypto_blinded_key_t *private_key,
                                      crypto_const_byte_buf_t input_message,
                                      eddsa_sign_mode_t sign_mode,
                                      crypto_word32_buf_t signature);

/**
 * Verifies an Ed25519 signature.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Input message to be signed for verification.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param signature Pointer to the signature to be verified.
 * @param[out] verification_result Result of signature verification
 * (Pass/Fail).
 * @return Result of the EdDSA verification operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_verify(
    const crypto_unblinded_key_t *public_key,
    crypto_const_byte_buf_t input_message, eddsa_sign_mode_t sign_mode,
    crypto_const_word32_buf_t signature, hardened_bool_t *verification_result);

/**
 * Generates a new key pair for X25519 key exchange.
 *
 * Computes the private scalar (d) and public key (Q) based on
 * Curve25519.
 *
 * No `domain_parameter` is needed and is automatically set for X25519.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. For hardware-backed keys, the keyblob length is 0 and the
 * keyblob pointer may be `NULL`. For non-hardware-backed keys, the keyblob
 * should be twice the length of the key. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the X25519 key generation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_x25519_keygen(crypto_blinded_key_t *private_key,
                                       crypto_unblinded_key_t *public_key);

/**
 * Performs the X25519 Diffie Hellman shared secret generation.
 *
 * @param private_key Pointer to blinded private key (u-coordinate).
 * @param public_key Pointer to the public scalar from the sender.
 * @param[out] shared_secret Pointer to shared secret key (u-coordinate).
 * @return Result of the X25519 operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_x25519(const crypto_blinded_key_t *private_key,
                                const crypto_unblinded_key_t *public_key,
                                crypto_blinded_key_t *shared_secret);

/**
 * Starts the asynchronous key generation for ECDSA operation.
 *
 * Initializes OTBN and begins generating an ECDSA key pair. The caller should
 * set the `config` field of `private_key` with their desired key configuration
 * options. If the key is hardware-backed, the caller should pass a fully
 * populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to `NULL`.
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous ECDSA keygen start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_keygen_async_start(
    const ecc_curve_t *elliptic_curve, const crypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for ECDSA operation.
 *
 * Returns `kCryptoStatusOK` and copies the private key (d) and public
 * key (Q), if the OTBN status is done, or
 * `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * The caller must ensure that the `elliptic_curve` parameter matches the one
 * that was previously passed to the corresponding `_start` function; a
 * mismatch will cause inconsistencies. Similarly, the private key
 * configuration must match the one originally passed to `_start`.
 *
 * @param elliptic_curve Pointer to the elliptic curve that is being used.
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of asynchronous ECDSA keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_keygen_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_blinded_key_t *private_key,
    crypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous ECDSA digital signature generation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message. The `domain_parameter` field of the
 * `elliptic_curve` is required only for a custom curve. For named
 * curves this field is ignored and can be set to `NULL`.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param message_digest Message digest to be signed (pre-hashed).
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @return Result of async ECDSA start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_sign_async_start(
    const crypto_blinded_key_t *private_key,
    const hash_digest_t *message_digest, const ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous ECDSA digital signature generation.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * The caller must ensure that the `elliptic_curve` parameter matches the one
 * that was previously passed to the corresponding `_start` function; a
 * mismatch will cause inconsistencies.
 *
 * @param elliptic_curve Pointer to the elliptic curve that is being used.
 * @param[out] signature Pointer to the signature struct with (r,s) values.
 * @return Result of async ECDSA finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_sign_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_word32_buf_t signature);

/**
 * Starts the asynchronous ECDSA digital signature verification.
 *
 * Initializes OTBN and starts the OTBN routine to recover ‘r’ value
 * from the input signature ‘s’ value. The `domain_parameter` field of
 * `elliptic_curve` is required only for a custom curve. For named
 * curves this field is ignored and can be set to `NULL`.
 *
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param message_digest Message digest to be verified (pre-hashed).
 * @param signature Pointer to the signature to be verified.
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @return Result of async ECDSA verify start function.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_verify_async_start(
    const crypto_unblinded_key_t *public_key,
    const hash_digest_t *message_digest, crypto_const_word32_buf_t signature,
    const ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous ECDSA digital signature verification.
 *
 * Returns `kCryptoStatusOK` and populates the `verification result`
 * if the OTBN status is done. `kCryptoStatusAsyncIncomplete` if the
 * OTBN is busy or `kCryptoStatusInternalError` if there is an error.
 * The computed signature is compared against the input signature
 * and a PASS or FAIL is returned.
 *
 * The caller must ensure that the `elliptic_curve` and `signature` parameters
 * matches the ones that were previously passed to the corresponding `_start`
 * function; a mismatch will cause inconsistencies.
 *
 * @param elliptic_curve Pointer to the elliptic curve that is being used.
 * @param[out] verification_result Result of signature verification
 * (Pass/Fail).
 * @return Result of async ECDSA verify finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdsa_verify_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result);

/**
 * Starts the asynchronous key generation for ECDH operation.
 *
 * Initializes OTBN and begins generating an ECDH key pair. The caller should
 * set the `config` field of `private_key` with their desired key configuration
 * options. If the key is hardware-backed, the caller should pass a fully
 * populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to `NULL`.
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous ECDH keygen start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdh_keygen_async_start(
    const ecc_curve_t *elliptic_curve, const crypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for ECDSA operation.
 *
 * Returns `kCryptoStatusOK` and copies the private key (d) and public
 * key (Q), if the OTBN status is done, or
 * `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * The caller must ensure that the `elliptic_curve` parameter matches the one
 * that was previously passed to the corresponding `_start` function; a
 * mismatch will cause inconsistencies. Similarly, the private key
 * configuration must match the one originally passed to `_start`.
 *
 * @param elliptic_curve Pointer to the elliptic curve that is being used.
 * @param[out] private_key Pointer to the blinded private key (d) struct.
 * @param[out] public_key Pointer to the unblinded public key (Q) struct.
 * @return Result of asynchronous ECDH keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdh_keygen_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_blinded_key_t *private_key,
    crypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous Elliptic Curve Diffie Hellman shared
 * secret generation.
 *
 * The `domain_parameter` field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to `NULL`.
 *
 * @param private_key Pointer to the blinded private key (d) struct.
 * @param public_key Pointer to the unblinded public key (Q) struct.
 * @param elliptic_curve Pointer to the elliptic curve to be used.
 * @return Result of async ECDH start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdh_async_start(
    const crypto_blinded_key_t *private_key,
    const crypto_unblinded_key_t *public_key,
    const ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous Elliptic Curve Diffie Hellman shared
 * secret generation.
 *
 * Returns `kCryptoStatusOK` and copies `shared_secret` if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN
 * is busy or `kCryptoStatusInternalError` if there is an error.
 *
 * The caller must ensure that the `elliptic_curve` parameter matches the one
 * that was previously passed to the corresponding `_start` function; a
 * mismatch will cause inconsistencies.
 *
 * @param elliptic_curve Pointer to the elliptic curve that is being used.
 * @param[out] shared_secret Pointer to generated blinded shared key struct.
 * @return Result of async ECDH finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ecdh_async_finalize(
    const ecc_curve_t *elliptic_curve, crypto_blinded_key_t *shared_secret);

/**
 * Starts the asynchronous key generation for Ed25519.
 *
 * Initializes OTBN and begins generating an Ed25519 key pair. The caller
 * should set the `config` field of `private_key` with their desired key
 * configuration options. If the key is hardware-backed, the caller should pass
 * a fully populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`.
 *
 * No `domain_parameter` is needed and is automatically set for X25519.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous ed25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_keygen_async_start(
    const crypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for Ed25519.
 *
 * Returns `kCryptoStatusOK` and copies private key (d) and public key
 * (Q), if the OTBN status is done, or `kCryptoStatusAsyncIncomplete`
 * if the OTBN is busy or `kCryptoStatusInternalError` if there is an
 * error.
 *
 * The caller must ensure that `config` matches the key configuration initially
 * passed to the `_start` complement of this function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous ed25519 keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous Ed25519 digital signature generation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message. The `domain_parameter` field for
 * Ed25519 is automatically set.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param input_message Input message to be signed.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param[out] signature Pointer to the EdDSA signature to get (r) value.
 * @return Result of async Ed25519 start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_byte_buf_t input_message, eddsa_sign_mode_t sign_mode,
    crypto_word32_buf_t signature);

/**
 * Finalizes the asynchronous Ed25519 digital signature generation.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param[out] signature Pointer to the EdDSA signature to get (s) value.
 * @return Result of async Ed25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_sign_async_finalize(
    crypto_word32_buf_t signature);

/**
 * Starts the asynchronous Ed25519 digital signature verification.
 *
 * Initializes OTBN and starts the OTBN routine to verify the
 * signature. The `domain_parameter` for Ed25519 is set automatically.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Input message to be signed for verification.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param signature Pointer to the signature to be verified.
 * @return Result of async Ed25519 verification start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_verify_async_start(
    const crypto_unblinded_key_t *public_key,
    crypto_const_byte_buf_t input_message, eddsa_sign_mode_t sign_mode,
    crypto_const_word32_buf_t signature);

/**
 * Finalizes the asynchronous Ed25519 digital signature verification.
 *
 * Returns `kCryptoStatusOK` and populates the `verification result`
 * with a PASS or FAIL, if the OTBN status is done,
 * `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * @param[out] verification_result Result of signature verification
 * (Pass/Fail).
 * @return Result of async Ed25519 verification finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result);

/**
 * Starts the asynchronous key generation for X25519.
 *
 * Initializes OTBN and begins generating an X25519 key pair. The caller
 * should set the `config` field of `private_key` with their desired key
 * configuration options. If the key is hardware-backed, the caller should pass
 * a fully populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`.
 *
 * No `domain_parameter` is needed and is automatically set for X25519.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous X25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_x25519_keygen_async_start(
    const crypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for X25519.
 *
 * Returns `kCryptoStatusOK` and copies private key (d) and public key
 * (Q), if the OTBN status is done, or `kCryptoStatusAsyncIncomplete`
 * if the OTBN is busy or `kCryptoStatusInternalError` if there is an
 * error.
 *
 * The caller must ensure that `config` matches the key configuration initially
 * passed to the `_start` complement of this function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous X25519 keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_x25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous X25519 Diffie Hellman shared secret
 * generation.
 *
 * Initializes OTBN and starts the OTBN routine to perform Diffie
 * Hellman shared secret generation based on Curve25519. The
 * domain parameter is automatically set for X25519 API.
 *
 * @param private_key Pointer to the blinded private key (u-coordinate).
 * @param public_key Pointer to the public scalar from the sender.
 * @return Result of the async X25519 start operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_x25519_async_start(
    const crypto_blinded_key_t *private_key,
    const crypto_unblinded_key_t *public_key);

/**
 * Finalizes the asynchronous X25519 Diffie Hellman shared secret
 * generation.
 *
 * Returns `kCryptoStatusOK` and copies `shared_secret` if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN
 * is busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param[out] shared_secret Pointer to shared secret key (u-coordinate).
 * @return Result of async X25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
crypto_status_t otcrypto_x25519_async_finalize(
    crypto_blinded_key_t *shared_secret);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_ECC_H_
