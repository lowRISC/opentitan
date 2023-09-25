// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_

#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"

/**
 * @file
 * @brief Message authentication codes for the OpenTitan cryptography library.
 *
 * Supports message authentication based on either HMAC or KMAC.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define KMAC mode.
 *
 * Values are hardened.
 */
typedef enum kmac_mode {
  // KMAC128 mode.
  kMacModeKmac128 = 0x336,
  // KMAC256 mode.
  kMacModeKmac256 = 0xec4,
} kmac_mode_t;

/**
 * Generic hmac context.
 *
 * Representation is internal to the hmac implementation; initialize
 * with #otcrypto_hmac_init.
 */
typedef struct hmac_context {
  hash_context_t inner;
  hash_context_t outer;
} hmac_context_t;

/**
 * Performs the HMAC function on the input data.
 *
 * This function computes the HMAC function on the `input_message` using the
 * `key` and returns a `tag`. The key should be at least as long as the digest
 * for the chosen hash function.. Only `kHashModeSha256`, `kHashModeSha384` and
 * `kHashModeSha512` are supported. Other modes (e.g. SHA-3) are not supported
 * and will result in errors.
 *
 * The caller should allocate 32 bytes (8 32-bit words) of space for the `tag`
 * buffer and set its `len` field to 8.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param hash_mode Hash function to use.
 * @param[out] tag Output authentication tag.
 * @return The result of the HMAC operation.
 */
crypto_status_t otcrypto_hmac(const crypto_blinded_key_t *key,
                              crypto_const_byte_buf_t input_message,
                              hash_mode_t hash_mode, crypto_word32_buf_t *tag);

/**
 * Performs the KMAC function on the input data.
 *
 * This function computes the KMAC on the `input_message` using the `key` and
 * returns a `tag` of `required_output_len`. The customization string is passed
 * through `customization_string` parameter. If no customization is desired it
 * can be empty.
 *
 * The caller should allocate enough space in the `tag` buffer to hold
 * `required_output_len` bytes, rounded up to the nearest word, and then set
 * the `len` field of `tag` to the word length. If the word length is not long
 * enough to hold `required_output_len` bytes, then the function will return an
 * error.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param mac_mode Required KMAC mode.
 * @param customization_string Customization string.
 * @param required_output_len Required output length, in bytes.
 * @param[out] tag Output authentication tag.
 * @return The result of the KMAC operation.
 */
crypto_status_t otcrypto_kmac(const crypto_blinded_key_t *key,
                              crypto_const_byte_buf_t input_message,
                              kmac_mode_t kmac_mode,
                              crypto_const_byte_buf_t customization_string,
                              size_t required_output_len,
                              crypto_word32_buf_t *tag);

/**
 * Performs the INIT operation for HMAC.
 *
 * Initializes the HMAC context. The key should be at least as long as the
 * digest for the chosen hash function. Only `kHashModeSha256`,
 * `kHashModeSha384` and `kHashModeSha512` are supported. Other modes (e.g.
 * SHA-3) are not supported and will result in errors.
 *
 * The HMAC streaming API supports only the `kMacModeHmacSha256` mode.  Other
 * modes are not supported and an error would be returned. The interface is
 * designed to be generic to support other required modes in the future.
 *
 * @param ctx Pointer to the generic HMAC context struct.
 * @param key Pointer to the blinded HMAC key struct.
 * @param hash_mode Hash function to use.
 * @return Result of the HMAC init operation.
 */
crypto_status_t otcrypto_hmac_init(hmac_context_t *ctx,
                                   const crypto_blinded_key_t *key,
                                   hash_mode_t hash_mode);

/**
 * Performs the UPDATE operation for HMAC.
 *
 * The update operation processes the `input_message` using the selected
 * compression function. The intermediate state is stored in the HMAC context
 * `ctx`. Any partial data is stored back in the context and combined with the
 * subsequent bytes.
 *
 * #otcrypto_hmac_init should be called before calling this function.
 *
 * @param ctx Pointer to the generic HMAC context struct.
 * @param input_message Input message to be hashed.
 * @return Result of the HMAC update operation.
 */
crypto_status_t otcrypto_hmac_update(hmac_context_t *const ctx,
                                     crypto_const_byte_buf_t input_message);

/**
 * Performs the FINAL operation for HMAC.
 *
 * The final operation processes the remaining partial blocks, computes the
 * final authentication code and copies it to the `tag` parameter.
 *
 * #otcrypto_hmac_update should be called before calling this function.
 *
 * The caller should allocate space for the `tag` buffer, (the length should
 * match the hash function digest size), and set the length of expected output
 * in the `len` field of `tag`. If the user-set length and the output length
 * does not match, an error message will be returned.
 *
 * @param ctx Pointer to the generic HMAC context struct.
 * @param[out] tag Output authentication tag.
 * @return Result of the HMAC final operation.
 */
crypto_status_t otcrypto_hmac_final(hmac_context_t *const ctx,
                                    crypto_word32_buf_t *tag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_
