// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KMAC_H_

#include "datatypes.h"

/**
 * @file
 * @brief Message authentication codes for the OpenTitan cryptography library.
 *
 * Supports message authentication based on either HMAC or KMAC.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of the KMAC context in words.
   *
   * Holds the key mode, the sideload flag and the driver-level context (two
   * words).
   *
   * TODO: Refine this once the save-and-context feature has landed.
   */
  kOtcryptoKmacCtxStructWords = 4,
};

/**
 * KMAC context struct maintained for streamed operations.
 *
 * TODO: Refine this once the save-and-restore feature has landed.
 */
typedef struct otcrypto_kmac_context {
  uint32_t data[kOtcryptoKmacCtxStructWords];
} otcrypto_kmac_context_t;

/**
 * Performs the KMAC function on the input data.
 *
 * This function computes the KMAC on the `input_message` using the `key` and
 * returns a `tag` of `required_output_len`. The customization string is passed
 * through `customization_string` parameter. If no customization is desired it
 * can be be left empty (by settings its `data` to NULL and `length` to 0).
 *
 * The caller should set the `key_length` field of `key.config` to the number
 * of bytes in the key. Only the following key sizes (in bytes) are supported:
 * [16, 24, 32, 48, 64]. If any other size is given, the function will return
 * `kOtcryptoStatusValueBadArgs`.
 *
 * The KMAC mode (KMAC-128 or KMAC-256) is inferred from the key mode.
 *
 * The caller should allocate enough space in the `tag` buffer to hold
 * `required_output_len` bytes, rounded up to the nearest word, and then set
 * the `len` field of `tag` to the word length. If the word length is not long
 * enough to hold `required_output_len` bytes, then the function will return
 * `kOtcryptoStatusValueBadArgs`.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param customization_string Customization string.
 * @param required_output_len Required output length, in bytes.
 * @param[out] tag Output authentication tag.
 * @return Result of the KMAC operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments, key configuration, or
 * buffer lengths are invalid, or `kOtcryptoStatusValueFatalError` if an
 * internal hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_kmac(
    otcrypto_blinded_key_t *key, const otcrypto_const_byte_buf_t *input_message,
    const otcrypto_const_byte_buf_t *customization_string,
    size_t required_output_len, otcrypto_word32_buf_t *tag);

/**
 * Perform the initialization operation for a streamed KMAC.
 *
 * The caller should set the `key_length` field of `key.config` to the number
 * of bytes in the key. Only the following key sizes (in bytes) are supported:
 * [16, 24, 32, 48, 64]. If any other size is given, the function will return
 * `kOtcryptoStatusValueBadArgs`.
 *
 * @param[out] ctx KMAC context.
 * @param key Pointer to the blinded key struct with key shares.
 * @param customization_string Customization string.
 * @return Result of the KMAC init operation. Returns `kOtcryptoStatusValueOk`
 * on success, `kOtcryptoStatusValueBadArgs` if arguments, key configuration,
 * or mode are invalid, or `kOtcryptoStatusValueFatalError` if an internal
 * hardware check fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_kmac_init(
    otcrypto_kmac_context_t *ctx, otcrypto_blinded_key_t *key,
    const otcrypto_const_byte_buf_t *customization_string);

/**
 * Update a streamed KMAC operation with an input message.
 *
 * The update operation streams the `input_message` into the KMAC hardware.
 * It may be called multiple times between `otcrypto_kmac_init` and
 * `otcrypto_kmac_final` invocations.
 *
 * @param ctx KMAC context.
 * @param input_message Input message to be authenticated.
 * @return Result of the KMAC update operation. Returns
 * `kOtcryptoStatusValueOk` on success, `kOtcryptoStatusValueBadArgs` if
 * arguments are invalid, or a recoverable error if the streaming operation
 * was interrupted by another use of the KMAC block.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_kmac_update(
    otcrypto_kmac_context_t *const ctx,
    const otcrypto_const_byte_buf_t *input_message);

/**
 * Finalize a streamed KMAC operation.
 *
 * The final operation computes the authentication tag of
 * `required_output_len` bytes and copies it to the `tag` parameter.
 *
 * The caller should allocate enough space in the `tag` buffer to hold
 * `required_output_len` bytes, rounded up to the nearest word, and then set
 * the `len` field of `tag` to the word length. If the word length is not long
 * enough to hold `required_output_len` bytes, then the function will return
 * `kOtcryptoStatusValueBadArgs`.
 *
 * @param ctx KMAC context.
 * @param required_output_len Required output length, in bytes.
 * @param[out] tag Output authentication tag.
 * @return Result of the KMAC final operation. Returns `kOtcryptoStatusValueOk`
 * on success, `kOtcryptoStatusValueBadArgs` if arguments or buffer lengths are
 * invalid, or `kOtcryptoStatusValueFatalError` if an internal hardware check
 * fails.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_kmac_final(otcrypto_kmac_context_t *const ctx,
                                      size_t required_output_len,
                                      otcrypto_word32_buf_t *tag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KMAC_H_
