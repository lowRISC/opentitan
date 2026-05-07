// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CMAC_H_

#include "datatypes.h"

/**
 * @file
 * @brief Cipher-based Message Authentication Codes (CMAC) for the OpenTitan
 * cryptography library.
 *
 * Supports message authentication based on AES-CMAC as specified in NIST SP
 * 800-38B.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of the base CMAC internal context in words.
   *
   * Holds key shares (0 and 1), lengths, sideload configuration, K1/K2 subkeys,
   * IV, and partial block states.
   */
  kOtcryptoCmacBaseCtxWords = 35,

  /**
   * Size of the exported CMAC context in words.
   *
   * Holds a security-level word, a primary cmac_ctx_t, and a redundant
   * cmac_ctx_t for medium/high security levels. For the low security
   * configuration only the primary slot is used.
   */
  kOtcryptoCmacCtxStructWords = 1 + 2 * kOtcryptoCmacBaseCtxWords,
};

/**
 * Generic CMAC context.
 *
 * Representation is internal to the CMAC implementation; initialize
 * with #otcrypto_cmac_init.
 */
typedef struct otcrypto_cmac_context {
  uint32_t data[kOtcryptoCmacCtxStructWords];
} otcrypto_cmac_context_t;

/**
 * Performs the CMAC function on the input data.
 *
 * This function computes the AES-CMAC function on the `input_message` using
 * the `key` and returns a `tag`. The key should be 128, 192, or 256 bits
 * in length.
 *
 * The caller should allocate space for the `tag` buffer and set the `len`
 * field of `tag` to the equivalent number of 32-bit words. According to NIST
 * SP 800-38B, the tag length must be at least 64 bits (2 words) and at most
 * 128 bits (4 words).
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be authenticated.
 * @param[out] tag Output authentication tag.
 * @return The result of the CMAC operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cmac(const otcrypto_blinded_key_t *key,
                                const otcrypto_const_byte_buf_t *input_message,
                                otcrypto_word32_buf_t *tag);

/**
 * Performs the INIT operation for CMAC.
 *
 * Initializes the CMAC context and derives the K1 and K2 subkeys. The key
 * should be an AES key of 128, 192, or 256 bits.
 *
 * @param[out] ctx Pointer to the generic CMAC context struct.
 * @param key Pointer to the blinded CMAC key struct.
 * @return Result of the CMAC init operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cmac_init(otcrypto_cmac_context_t *ctx,
                                     const otcrypto_blinded_key_t *key);

/**
 * Performs the UPDATE operation for CMAC.
 *
 * The update operation processes the `input_message` using the AES block
 * cipher. The intermediate IV state is stored in the CMAC context `ctx`.
 * Any partial data is stored back in the context and combined with the
 * subsequent bytes.
 *
 * #otcrypto_cmac_init should be called before calling this function.
 *
 * @param ctx Pointer to the generic CMAC context struct.
 * @param input_message Input message to be authenticated.
 * @return Result of the CMAC update operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cmac_update(
    otcrypto_cmac_context_t *const ctx,
    const otcrypto_const_byte_buf_t *input_message);

/**
 * Performs the FINAL operation for CMAC.
 *
 * The final operation processes the remaining partial block (applying
 * either the K1 or K2 subkey depending on block alignment), computes the
 * final authentication code, and copies it to the `tag` parameter.
 *
 * #otcrypto_cmac_update should be called before calling this function.
 *
 * The caller should allocate space for the `tag` buffer and set the length
 * of expected output in the `len` field of `tag`. The length must be between
 * 2 and 4 words inclusive.
 *
 * @param ctx Pointer to the generic CMAC context struct.
 * @param[out] tag Output authentication tag.
 * @return Result of the CMAC final operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cmac_final(otcrypto_cmac_context_t *const ctx,
                                      otcrypto_word32_buf_t *tag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CMAC_H_
