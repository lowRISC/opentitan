// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HASH_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HASH_H_

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * @file
 * @brief Hash functions for the OpenTitan cryptography library.
 *
 * Supports both SHA2 and SHA3 hash functions, plus the additional Keccak-based
 * hash functions SHAKE and cSHAKE.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define supported hashing modes.
 *
 * Values are hardened.
 */
typedef enum hash_mode {
  // SHA2-256 mode.
  kHashModeSha256 = 0x6dc2,
  // SHA2-384 mode.
  kHashModeSha384 = 0xdafb,
  // SHA2-512 mode.
  kHashModeSha512 = 0xb626,
  // SHA3-224 mode.
  kHashModeSha3_224 = 0xf51d,
  // SHA3-256 mode.
  kHashModeSha3_256 = 0x196e,
  // SHA3-384 mode.
  kHashModeSha3_384 = 0x14f5,
  // SHA3-512 mode.
  kHashModeSha3_512 = 0x62cd,
} hash_mode_t;

/**
 * Enum to define the supported extendable-output functions.
 *
 * Values are hardened.
 */
typedef enum xof_mode {
  // Shake128 mode.
  kXofModeSha3Shake128 = 0x2bb4,
  // Shake256 mode.
  kXofModeSha3Shake256 = 0x4778,
  // cShake128 mode.
  kXofModeSha3Cshake128 = 0x8f45,
  // cShake256 mode.
  kXofModeSha3Cshake256 = 0x8c9e,
} xof_mode_t;

/**
 * Generic hash context.
 *
 * Representation is internal to the hash implementation; initialize
 * with #otcrypto_hash_init.
 */
typedef struct hash_context {
  hash_mode_t mode;
  uint32_t data[52];
} hash_context_t;

/**
 * Performs the required hash function on the input data.
 *
 * The caller should allocate space for the `digest` buffer, (expected
 * length depends on `hash_mode`, refer table-1), and set the length
 * of expected output in the `len` field of `digest`. If the user-set
 * length and the output length does not match, an error message will
 * be returned.
 *
 * This function hashes the `input_message` using the `hash_mode_t`
 * hash function and returns a `digest`.
 *
 * @param input_message Input message to be hashed.
 * @param hash_mode Required hash mode for the digest.
 * @param[out] digest Output digest after hashing the input message.
 * @return Result of the hash operation.
 */
crypto_status_t otcrypto_hash(crypto_const_uint8_buf_t input_message,
                              hash_mode_t hash_mode,
                              crypto_uint8_buf_t *digest);

/**
 * Performs the required extendable output function on the input data.
 *
 * The `function_name_string` is used by NIST to define functions
 * based on cSHAKE. When no function other than cSHAKE is desired; it
 * can be empty. The `customization_string` is used to define a
 * variant of the cSHAKE function. If no customization is desired it
 * can be empty. The `function_name_string` and `customization_string`
 * are ignored when the `xof_mode` is set to kHashModeSha3Shake128 or
 * kHashModeSha3Shake256.
 *
 * The caller should allocate space for the `digest` buffer,
 * (expected length same as `required_output_len`), and set the length
 * of expected output in the `len` field of `digest`. If the user-set
 * length and the output length does not match, an error message will
 * be returned.
 *
 * @param input_message Input message for extendable output function.
 * @param hash_mode Required extendable output function.
 * @param function_name_string NIST Function name string.
 * @param customization_string Customization string for cSHAKE.
 * @param required_output_len Required output length, in bytes.
 * @param[out] digest Output from the extendable output function.
 * @return Result of the xof operation.
 */
crypto_status_t otcrypto_xof(crypto_const_uint8_buf_t input_message,
                             xof_mode_t xof_mode,
                             crypto_const_uint8_buf_t function_name_string,
                             crypto_const_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *digest);

/**
 * Performs the INIT operation for a cryptographic hash function.
 *
 * Initializes the generic hash context. The required hash mode is
 * selected through the `hash_mode` parameter. Only `kHashModeSha256`,
 * `kHashModeSha384` and `kHashModeSha512` are supported. Other modes
 * are not supported and an error would be returned.
 *
 * Populates the hash context with the selected hash mode and its
 * digest and block sizes. The structure of hash context and how it
 * populates the required fields are internal to the specific hash
 * implementation.
 *
 * @param ctx Pointer to the generic hash context struct.
 * @param hash_mode Required hash mode.
 * @return Result of the hash init operation.
 */
crypto_status_t otcrypto_hash_init(hash_context_t *const ctx,
                                   hash_mode_t hash_mode);

/**
 * Performs the UPDATE operation for a cryptographic hash function.
 *
 * The update operation processes the `input_message` using the selected
 * hash compression function. The intermediate digest is stored in the
 * context `ctx`. Any partial data is stored back in the context and
 * combined with the subsequent bytes.
 *
 * #otcrypto_hash_init should be called before this function.
 *
 * @param ctx Pointer to the generic hash context struct.
 * @param input_message Input message to be hashed.
 * @return Result of the hash update operation.
 */
crypto_status_t otcrypto_hash_update(hash_context_t *const ctx,
                                     crypto_const_uint8_buf_t input_message);

/**
 * Performs the FINAL operation for a cryptographic hash function.
 *
 * The final operation processes the remaining partial blocks,
 * computes the final hash and copies it to the `digest` parameter.
 *
 * #otcrypto_hash_update should be called before this function.
 *
 * The caller should allocate space for the `digest` buffer, (expected
 * length depends on `hash_mode`, refer table-1), and set the length
 * of expected output in the `len` field of `digest`. If the user-set
 * length and the output length does not match, an error message will
 * be returned.
 *
 * @param ctx Pointer to the generic hash context struct.
 * @param[out] digest Output digest after hashing the input blocks.
 * @return Result of the hash final operation.
 */
crypto_status_t otcrypto_hash_final(hash_context_t *const ctx,
                                    crypto_uint8_buf_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HASH_H_
