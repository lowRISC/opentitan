// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA3_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA3_H_

#include "datatypes.h"

/**
 * @file
 * @brief Keccak-based hash functions for the OpenTitan cryptography library.
 *
 * Supports SHA3, SHAKE, and cSHAKE operations.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of the SHA-3 context in words.
   *
   * Holds the driver-level context (four words).
   *
   * TODO: Refine this once the save-and-context feature has landed.
   */
  kOtcryptoSha3CtxStructWords = 4,
};

/**
 * SHA3 context struct maintained for streamed operations.
 *
 * TODO: Refine this once the save-and-context feature has landed.
 */
typedef struct otcrypto_sha3_context {
  uint32_t data[kOtcryptoSha3CtxStructWords];
} otcrypto_sha3_context_t;

/**
 * One-shot SHA3-224 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 224
 * bits (= 7 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-224 operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_224(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA3-256 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 256
 * bits (= 8 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-256 operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_256(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA3-384 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 384
 * bits (= 12 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-384 operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_384(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA3-512 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 512
 * bits (= 16 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-512 operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_512(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHAKE128 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return Result of the SHAKE128 operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake128(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHAKE256 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return Result of the SHAKE256 operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake256(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot cSHAKE128 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * The function name and customization string parameters are defined in NIST
 * SP800-185; please refer to that document for guidance on their usage.
 *
 * @param message Input message.
 * @param function_name_string Function name parameter (may be empty).
 * @param customization_string Customization parameter (may be empty).
 * @param[out] digest Computed digest.
 * @return Result of the cSHAKE128 operation. Returns `kOtcryptoStatusValueOk`
 * on success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake128(
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *function_name_string,
    const otcrypto_const_byte_buf_t *customization_string,
    otcrypto_hash_digest_t *digest);

/**
 * One-shot cSHAKE256 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * The function name and customization string parameters are defined in NIST
 * SP800-185; please refer to that document for guidance on their usage.
 *
 * @param message Input message.
 * @param function_name_string Function name parameter (may be empty).
 * @param customization_string Customization parameter (may be empty).
 * @param[out] digest Computed digest.
 * @return Result of the cSHAKE256 operation. Returns `kOtcryptoStatusValueOk`
 * on success, `kOtcryptoStatusValueBadArgs` if arguments or digest length are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake256(
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *function_name_string,
    const otcrypto_const_byte_buf_t *customization_string,
    otcrypto_hash_digest_t *digest);

/**
 * Perform the initialization operation for a streamed SHA3-224 computation.
 *
 * @param[out] ctx SHA3 context.
 * @return Result of the SHA3-224 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_224_init(otcrypto_sha3_context_t *ctx);

/**
 * Perform the initialization operation for a streamed SHA3-256 computation.
 *
 * @param[out] ctx SHA3 context.
 * @return Result of the SHA3-256 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_256_init(otcrypto_sha3_context_t *ctx);

/**
 * Perform the initialization operation for a streamed SHA3-384 computation.
 *
 * @param[out] ctx SHA3 context.
 * @return Result of the SHA3-384 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_384_init(otcrypto_sha3_context_t *ctx);

/**
 * Perform the initialization operation for a streamed SHA3-512 computation.
 *
 * @param[out] ctx SHA3 context.
 * @return Result of the SHA3-512 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_512_init(otcrypto_sha3_context_t *ctx);

/**
 * Perform the initialization operation for a streamed SHAKE128 computation.
 *
 * @param[out] ctx SHA3 context.
 * @return Result of the SHAKE128 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake128_init(otcrypto_sha3_context_t *ctx);

/**
 * Perform the initialization operation for a streamed SHAKE256 computation.
 *
 * @param[out] ctx Pointer to the generic SHA-3 context struct.
 * @return Result of the SHAKE256 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake256_init(otcrypto_sha3_context_t *ctx);

/**
 * Perform the initialization operation for a streamed cSHAKE128 computation.
 *
 * The function name and customization string parameters are defined in NIST
 * SP800-185; please refer to that document for guidance on their usage.
 *
 * @param[out] ctx SHA3 context.
 * @param function_name_string Function name parameter (may be empty).
 * @param customization_string Customization parameter (may be empty).
 * @return Result of the cSHAKE128 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake128_init(
    otcrypto_sha3_context_t *ctx,
    const otcrypto_const_byte_buf_t *function_name_string,
    const otcrypto_const_byte_buf_t *customization_string);

/**
 * Perform the initialization operation for a streamed cSHAKE256 computation.
 *
 * The function name and customization string parameters are defined in NIST
 * SP800-185; please refer to that document for guidance on their usage.
 *
 * @param[out] ctx SHA3 context.
 * @param function_name_string Function name parameter (may be empty).
 * @param customization_string Customization parameter (may be empty).
 * @return Result of the cSHAKE256 init operation. Returns
 * `kOtcryptoStatusValueOk` on success, or `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake256_init(
    otcrypto_sha3_context_t *ctx,
    const otcrypto_const_byte_buf_t *function_name_string,
    const otcrypto_const_byte_buf_t *customization_string);

/**
 * Update a streamed SHA-3 operation with an input message.
 *
 * The update operation streams the `input_message` into the Keccak hardware.
 * It can be called multiple times between the init and final invocations.
 *
 * @param ctx SHA3 context.
 * @param input_message Input message to be hashed.
 * @return Result of the SHA-3 update operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid, or a recoverable error if the streaming operation
 * was interrupted by another use of the KMAC block.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_update(
    otcrypto_sha3_context_t *const ctx,
    const otcrypto_const_byte_buf_t *input_message);

/**
 * Perform the finalization operation for a streamed SHA3-224 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 224
 * bits (= 7 32-bit words). The `digest.mode` field is set by this function
 * and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-224 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_224_final(otcrypto_sha3_context_t *const ctx,
                                          otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed SHA3-256 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 256
 * bits (= 8 32-bit words). The `digest.mode` field is set by this function
 * and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-256 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_256_final(otcrypto_sha3_context_t *const ctx,
                                          otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed SHA3-384 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 384
 * bits (= 12 32-bit words). The `digest.mode` field is set by this function
 * and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-384 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_384_final(otcrypto_sha3_context_t *const ctx,
                                          otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed SHA3-512 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 512
 * bits (= 16 32-bit words). The `digest.mode` field is set by this function
 * and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the SHA3-512 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_512_final(otcrypto_sha3_context_t *const ctx,
                                          otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed SHAKE128 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter. The context is invalidated on return and may not be used again.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the SHAKE128 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake128_final(otcrypto_sha3_context_t *const ctx,
                                          otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed SHAKE256 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter. The context is invalidated on return and may not be used again.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the SHAKE256 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake256_final(otcrypto_sha3_context_t *const ctx,
                                          otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed cSHAKE128 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter. The context is invalidated on return and may not be used again.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the cSHAKE128 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake128_final(otcrypto_sha3_context_t *const ctx,
                                           otcrypto_hash_digest_t *digest);

/**
 * Perform the finalization operation for a streamed cSHAKE256 computation.
 *
 * The final operation computes the digest and copies it to the `digest`
 * parameter. The context is invalidated on return and may not be used again.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param ctx SHA3 context.
 * @param[out] digest Computed digest.
 * @return Result of the cSHAKE256 final operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments or digest length are invalid, or `kOtcryptoStatusValueFatalError`
 * if an internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake256_final(otcrypto_sha3_context_t *const ctx,
                                           otcrypto_hash_digest_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA3_H_
