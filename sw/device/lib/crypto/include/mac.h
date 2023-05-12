// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_

#include "sw/device/lib/crypto/include/datatypes.h"

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
  kMacModeKmac128 = 0x69b6,
  // KMAC256 mode.
  kMacModeKmac256 = 0xee62,
} kmac_mode_t;

/**
 * Generic hmac context.
 *
 * Representation is internal to the hmac implementation; initialize
 * with #otcrypto_hmac_init.
 */
typedef struct hmac_context {
  uint32_t data[42];
} hmac_context_t;

/**
 * Generates a new HMAC or KMAC key.
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
 * @param[out] key Destination blinded key struct.
 * @return The result of the key generation operation.
 */
crypto_status_t otcrypto_mac_keygen(crypto_blinded_key_t *key);

/**
 * Performs the HMAC-SHA256 function on the input data.
 *
 * This function computes the required MAC function on the `input_message`
 * using the `key` and returns a `tag`.
 *
 * The caller should allocate 32 bytes of space for the `tag` buffer and set
 * its `len` field to 32.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param[out] tag Output authentication tag.
 * @return The result of the HMAC operation.
 */
crypto_status_t otcrypto_hmac(const crypto_blinded_key_t *key,
                              crypto_const_uint8_buf_t input_message,
                              crypto_uint8_buf_t *tag);

/**
 * Performs the KMAC function on the input data.
 *
 * This function computes the KMAC on the `input_message` using the `key` and
 * returns a `tag` of `required_output_len`. The customization string is passed
 * through `customization_string` parameter. If no customization is desired it
 * can be empty. The `customization_string` and `required_output_len` is only
 * used for KMAC modes and is ignored for the HMAC mode.
 *
 * The caller should allocate `required_output_len` bytes for the `tag` buffer
 * and set the `len` field of `tag` to `required_output_len`. If the user-set
 * length and the output length does not match, an error message will be
 * returned.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param mac_mode Required operation to be performed.
 * @param customization_string Customization string.
 * @param required_output_len Required output length, in bytes.
 * @param[out] tag Output authentication tag.
 * @return The result of the KMAC operation.
 */
crypto_status_t otcrypto_kmac(const crypto_blinded_key_t *key,
                              crypto_const_uint8_buf_t input_message,
                              kmac_mode_t kmac_mode,
                              crypto_const_uint8_buf_t customization_string,
                              size_t required_output_len,
                              crypto_uint8_buf_t *tag);

/**
 * Performs the INIT operation for HMAC.
 *
 * Initializes the generic HMAC context. The required HMAC mode is selected
 * through the `hmac_mode` parameter. The structure of HMAC context and how it
 * populates the required fields based on the HMAC mode are internal to the
 * specific HMAC implementation.
 *
 * The HMAC streaming API supports only the `kMacModeHmacSha256` mode.  Other
 * modes are not supported and an error would be returned. The interface is
 * designed to be generic to support other required modes in the future.
 *
 * @param ctx Pointer to the generic HMAC context struct.
 * @param key Pointer to the blinded HMAC key struct.
 * @return Result of the HMAC init operation.
 */
crypto_status_t otcrypto_hmac_init(hmac_context_t *ctx,
                                   const crypto_blinded_key_t *key);

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
                                     crypto_const_uint8_buf_t input_message);

/**
 * Performs the FINAL operation for HMAC.
 *
 * The final operation processes the remaining partial blocks, computes the
 * final authentication code and copies it to the `tag` parameter.
 *
 * #otcrypto_hmac_update should be called before calling this function.
 *
 * The caller should allocate space for the `tag` buffer, (expected length is
 * 32 bytes for HMAC), and set the length of expected output in the `len` field
 * of `tag`. If the user-set length and the output length does not match, an
 * error message will be returned.
 *
 * @param ctx Pointer to the generic HMAC context struct.
 * @param[out] tag Output authentication tag.
 * @return Result of the HMAC final operation.
 */
crypto_status_t otcrypto_hmac_final(hmac_context_t *const ctx,
                                    crypto_uint8_buf_t *tag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MAC_H_
