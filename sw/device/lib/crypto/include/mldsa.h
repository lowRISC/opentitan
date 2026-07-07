// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MLDSA_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MLDSA_H_

#include "datatypes.h"

/**
 * @file
 * @brief ML-DSA operations for OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of a ML-DSA-87 public key.
   */
  kOtcryptoMldsa87PkBytes = 2592,
  kOtcryptoMldsa87PkWords = kOtcryptoMldsa87PkBytes / sizeof(uint32_t),
  /**
   * Size of a Boolean-masked ML-DSA-87 secret key.
   */
  kOtcryptoMldsa87SkBytes = 6368,
  kOtcryptoMldsa87SkWords = kOtcryptoMldsa87SkBytes / sizeof(uint32_t),
  /**
   * Size of a ML-DSA-87 signature with 1-byte zero-padding.
   */
  kOtcryptoMldsa87SigBytes = 4627 + 1,
  kOtcryptoMldsa87SigWords = kOtcryptoMldsa87SigBytes / sizeof(uint32_t),
  /**
   * Maximum size of a ML-DSA context string.
   */
  kOtcryptoMldsa87CtxMaxBytes = 255,
  /**
   * Maximum size of a ML-DSA message.
   */
  kOtcryptoMldsa87MsgMaxBytes = 8192,
};

/**
 * Hashing modes for ML-DSA sign and verify.
 *
 * ML-DSA makes a distinction between pure mode hashing, where the message
 * representative `mu` is derived directly from the raw input message through
 * the application of the SHAKE256 XOF, and a pre-hash mode where `mu` is
 * computed from a digest of the message. A set of two hash functions and one
 * XOF are permitted for the computation of this digest. The standard makes it
 * clear that pure mode hashing is preferred and that pre-hash mode should
 * only be used in implementations where the SHAKE256 XOF poses a bottleneck.
 *
 * Note that in pure mode, `mu` is computed on the host CPU and not OTBN due
 * to the arbitrary size of the message. This is not a security issue as only
 * public-key material is required.
 */
typedef enum otcrypto_mldsa_hash_mode {
  // Magic constants generated with:
  // ./util/design/sparse-fsm-encode.py --avoid-zero --seed 987654321 \
  //    --distance 10 --states 10 --bits 20

  // Pure mode hashing.
  kOtcryptoMldsaHashModePure = 0xe4fd3000,
  // Supported pre-hash modes. Bits 0-3 encode the hash OID, bits 4-11 encode
  // the digest length in bytes. For more information on the OID see
  // https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
  kOtcryptoMldsaHashModeSha2_256 = 0xdea7c201,
  kOtcryptoMldsaHashModeSha2_384 = 0x7c98e302,
  kOtcryptoMldsaHashModeSha2_512 = 0x3b329403,
  kOtcryptoMldsaHashModeSha3_224 = 0x4bc371c7,
  kOtcryptoMldsaHashModeSha3_256 = 0x9456f208,
  kOtcryptoMldsaHashModeSha3_384 = 0xc37e4309,
  kOtcryptoMldsaHashModeSha3_512 = 0x71cf840a,
  kOtcryptoMldsaHashModeShake128 = 0xb7c8520b,
  kOtcryptoMldsaHashModeShake256 = 0x2f2d620c,
  // Unsupported pre-hash modes: SHA2_224, SHA2_256/224 and SHA2_512/256.
} otcrypto_mldsa_hash_mode_t;

/**
 * ML-DSA signing modes.
 *
 * The standard specifies two signing modes, random (hedged) and deterministic.
 * In the random mode, the application samples fresh randomness for every new
 * signature generation, while in deterministic mode the randomness is the zero
 * string.
 *
 * Although allowed by the standard, the deterministic mode *MUST NEVER* be
 * used in security-relevant applications, preferably only testing should make
 * use of it.
 */
typedef enum otcrypto_mldsa_sign_mode {
  // Magic constants generated with:
  // ./util/design/sparse-fsm-encode.py --avoid-zero --seed 123456789
  //    --distance 16 --states 2 --bits 32

  kOtcryptoMldsaSignModeRnd = 0x7138777c,
  kOtcryptoMldsaSignModeDet = 0x8accea7f,
} otcrypto_mldsa_sign_mode_t;

/**
 * Generates a key pair for ML-DSA-87 (WIP not yet finalized).
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob.
 *
 * The partially shared private key (6304 bytes) consists of the following
 * fields starting from the least significant byte:
 *
 *   - rho: 32 bytes
 *   - K (share 0): 32 bytes
 *   - K (share 1): 32 bytes
 *   - s1 (share 0): 672 bytes
 *   - s1 (share 1): 672 bytes
 *   - s2 (share 0): 768 bytes
 *   - s2 (share 1): 768 bytes
 *   - t0: 3328 bytes
 *
 * The public key (2592 bytes) consists of the fields listed below:
 *
 *   - rho: 32 bytes
 *   - t1: 2560 bytes
 *
 * @param[out] private_key Pointer to the partially shared private key struct.
 * @param[out] public_key Pointer to the unshared public key struct.
 * @param Result of the ML-DSA-87 key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_keygen(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key);

/**
 * Generates a ML-DSA-87 digital signature.
 *
 * The signature (4627+ 1 bytes) consists of the following fields starting from
 * the least significant byte:
 *
 *   - c_tilde: 64 bytes
 *   - z: 6368 bytes (rho (32B), K (32B, bool share 0), K (32B, bool share 1),
 *       tr (64B), s1 (672B, bool share 0), s1, (672B, bool share 1), s2
 *       (768B, bool share 0), s2 (768B, bool share 1), t0 (3328B))
 *   - hint: 83 + 1 bytes
 *
 * For protection against FI attacks, the ML-DSA sign OTBN app is executed
 * twice and the two resulting signatures are checked for equality.
 *
 * Do not use the deterministic signing mode for anything other than testing.
 *
 * @param private_key Pointer to the partially shared private key struct.
 * @param message Message to be signed.
 * @param context Context string (must be at most 255 bytes).
 * @param hash_mode ML-DSA hashing mode (pure or pre-hash).
 * @param sign_mode ML-DSA signing mode (random or deterministic).
 * @param[out] signature Pointer to the ML-DSA-87 signature.
 * @return Result of the ML-DSA-87 signature.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_mldsa_sign_mode_t sign_mode,
    otcrypto_word32_buf_t *signature);

/**
 * Verifies a ML-DSA-87 signature.
 *
 * The caller must check the `verification_result` parameter, NOT only the
 * returned status code, to know if the signature passed verification. The
 * status code, as for other operations, only indicates whether errors were
 * encountered, and may return OK even when the signature is invalid.
 *
 * @param public_key Pointer to the unshared public key.
 * @param message Message to be signed for verification.
 * @param context Context string (max 255 bytes).
 * @param signature Pointer to the signature to be verified.
 * @param hash_mode ML-DSA hashing mode (pure or pre-hash).
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of the Ed25519 verification operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    const otcrypto_const_word32_buf_t *signature,
    otcrypto_mldsa_hash_mode_t hash_mode, hardened_bool_t *verification_result);

/**
 * Verifies whether the public and private key belong together (WIP not yet
 * finalized).
 *
 * The caller must check the `verification_result` parameter, NOT only the
 * returned status code, to know if the keycheck was successful. The
 * status code, as for other operations, only indicates whether errors were
 * encountered, and may return OK even when the signature is invalid.
 *
 * @param public_key Pointer to the unshared public key.
 * @param private_key Pointer to the partially shared private key struct.
 * @param[out] keycheck_result Whether the keycheck was successful.
 * @return Result of the ML-DSA-87 keycheck operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_keycheck(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result);

/**
 * Starts asynchronous key generation for ML-DSA-87 (WIP not yet finalized).
 *
 * See `otcrypto_mldsa87_keygen` for requirements on input values.
 *
 * @param[out] private_key Pointer to the partially shared private key struct.
 * @param[out] public_key Pointer to the unshared public key struct.
 * @param Result of the ML-DSA-87 key generation start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_keygen_async_start(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key);

/**
 * Finalizes asynchronous key generation for ML-DSA-87 (WIP not yet finalized).
 *
 * See `otcrypto_mldsa87_keygen` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] private_key Pointer to the partially shared private key struct.
 * @param[out] public_key Pointer to the unshared public key struct.
 * @param Result of the ML-DSA-87 key generation finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_keygen_async_finalize(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key);

/**
 * Starts asynchronous signature generation for ML-DSA-87.
 *
 * Do not use the deterministic signing mode for anything other than testing.
 *
 * See `otcrypto_mldsa87_sign` for requirements on the input values.
 *
 * @param private_key Pointer to the partially shared private key struct.
 * @param message Message to be signed.
 * @param context Context string (must be at most 255 bytes).
 * @param hash_mode ML-DSA hashing mode (pure or pre-hash).
 * @param sign_mode ML-DSA signing mode (random or deterministic).
 * @return Result of the ML-DSA-87 signature generation start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_mldsa_sign_mode_t sign_mode);

/**
 * Finalizes asynchronous signature generation for ML-DSA-87.
 *
 * See `otcrypto_mldsa87_sign` for requirements on the input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] signature Pointer to the ML-DSA-87 signature.
 * @return Result of the ML-DSA-87 signature generation finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_sign_async_finalize(
    otcrypto_word32_buf_t *signature);

/**
 * Finalizes asynchronous signature generation for ML-DSA-87.
 *
 * A second redundant sign is executed following the completion of the first
 * one for FI protection. See `otcrypto_mldsa87_sign` for requirements on the
 * input values.
 *
 * May block until the operation is complete.
 *
 * @param[out] signature Pointer to the ML-DSA-87 signature.
 * @return Result of the ML-DSA-87 signature generation finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_double_sign_async_finalize(
    otcrypto_word32_buf_t *signature);

/**
 * Starts asynchronous signature verification for ML-DSA-87.
 *
 * See `otcrypto_mldsa87_verify` for requirements on input values.
 *
 * @param public_key Pointer to the unshared public key.
 * @param message Message to be signed for verification.
 * @param context Context string (must be at most 255 bytes).
 * @param hash_mode ML-DSA hashing mode (pure or pre-hash).
 * @param signature Pointer to the signature to be verified.
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of the Ed25519 signature verification start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    const otcrypto_const_word32_buf_t *signature,
    otcrypto_mldsa_hash_mode_t hash_mode);

/**
 * Finalizes asynchronous signature verification for ML-DSA-87.
 *
 * See `otcrypto_mldsa87_verify` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param public_key Pointer to the unshared public key.
 * @param message Message to be signed for verification.
 * @param context Context string (must be at most 255 bytes).
 * @param hash_mode ML-DSA hashing mode (pure or pre-hash).
 * @param signature Pointer to the signature to be verified.
 * @param[out] verification_result Whether the signature passed verification.
 * @return Result of the Ed25519 signature verification finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_verify_async_finalize(
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result);

/**
 * Starts asynchronous keycheck operation for ML-DSA-87 (WIP not yet finalized).
 *
 * See `otcrypto_mldsa87_keycheck` for requirements on input values.
 *
 * @param public_key Pointer to the unshared public key.
 * @param private_key Pointer to the partially shared private key struct.
 * @param[out] keycheck_result Whether the keycheck was successful.
 * @return Result of the ML-DSA-87 keycheck start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_keycheck_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result);

/**
 * Finalizes asynchronous keycheck operation for ML-DSA-87 (WIP not yet
 * finalized).
 *
 * See `otcrypto_mldsa87_keycheck` for requirements on input values.
 *
 * May block until the operation is complete.
 *
 * @param public_key Pointer to the unshared public key.
 * @param private_key Pointer to the partially shared private key struct.
 * @param[out] keycheck_result Whether the keycheck was successful.
 * @return Result of the ML-DSA-87 keycheck finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mldsa87_keycheck_async_finalize(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MLDSA_H_
