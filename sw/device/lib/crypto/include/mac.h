// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_

#include "datatypes.h"
#include "hash.h"

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
typedef enum otcrypto_kmac_mode {
  // KMAC128 mode.
  kOtcryptoKmacModeKmac128 = 0x336,
  // KMAC256 mode.
  kOtcryptoKmacModeKmac256 = 0xec4,
} otcrypto_kmac_mode_t;

/**
 * Generic hmac context.
 *
 * Representation is internal to the hmac implementation; initialize
 * with #otcrypto_hmac_init.
 */
typedef struct otcrypto_hmac_context {
  otcrypto_hash_context_t inner;
  otcrypto_hash_context_t outer;
} otcrypto_hmac_context_t;

/**
 * Performs the HMAC function on the input data.
 *
 * This function computes the HMAC function on the `input_message` using the
 * `key` and returns a `tag`. The key should be at least as long as the digest
 * for the chosen hash function. The hash function is determined by the key
 * mode. Only SHA-2 hash functions are supported. Other modes (e.g. SHA-3) are
 * not supported and will result in errors.
 *
 * The caller should allocate the following amount of space for the `tag`
 * buffer, depending on which hash algorithm is used:
 *
 * SHA-256: 32 bytes
 * SHA-384: 48 bytes
 * SHA-512: 64 bytes
 *
 * The caller should also set the `len` field of `tag` to the equivalent number
 * of 32-bit words (e.g. 8 for SHA-256).
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param[out] tag Output authentication tag.
 * @return The result of the HMAC operation.
 */
otcrypto_status_t otcrypto_hmac(const otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_word32_buf_t tag);

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
 * an error.
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
otcrypto_status_t otcrypto_kmac(const otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_kmac_mode_t kmac_mode,
                                otcrypto_const_byte_buf_t customization_string,
                                size_t required_output_len,
                                otcrypto_word32_buf_t tag);

/**
 * Performs the INIT operation for HMAC.
 *
 * Initializes the HMAC context. The key should be at least as long as the
 * digest for the chosen hash function. The hash function is determined by the
 * key mode. Only SHA-2 hash functions are are supported. Other modes (e.g.
 * SHA-3) are not supported and will result in errors.
 *
 * @param[out] ctx Pointer to the generic HMAC context struct.
 * @param key Pointer to the blinded HMAC key struct.
 * @param hash_mode Hash function to use.
 * @return Result of the HMAC init operation.
 */
otcrypto_status_t otcrypto_hmac_init(otcrypto_hmac_context_t *ctx,
                                     const otcrypto_blinded_key_t *key);

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
otcrypto_status_t otcrypto_hmac_update(otcrypto_hmac_context_t *const ctx,
                                       otcrypto_const_byte_buf_t input_message);

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
otcrypto_status_t otcrypto_hmac_final(otcrypto_hmac_context_t *const ctx,
                                      otcrypto_word32_buf_t tag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_
