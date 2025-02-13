// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA2_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA2_H_

#include "datatypes.h"

/**
 * @file
 * @brief SHA-2 hash functions for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * The size of the publicly exposed HMAC context in words.
   * We assert that this value is large enough to host the internal HMAC driver
   * struct.
   */
  kOtcryptoSha2CtxStructWords = 87,
};

/**
 * Opaque SHA-2 hash context.
 *
 * Representation is internal to the hash implementation; initialize
 * with #otcrypto_sha2_init.
 */
typedef struct otcrypto_sha2_context {
  uint32_t data[kOtcryptoSha2CtxStructWords];
} otcrypto_sha2_context_t;

/**
 * One-shot SHA2-256 hash computation.
 *
 * The caller should allocate space for the `digest` buffer and set the `len`
 * fields. If the length does not match the mode, an error message will be
 * returned. The `mode` field will be set by this function.
 *
 * @param message Input message to be hashed.
 * @param[out] digest Output digest after hashing the input message.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha2_256(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA2-384 hash computation.
 *
 * The caller should allocate space for the `digest` buffer and set the `len`
 * fields. If the length does not match the mode, an error message will be
 * returned. The `mode` field will be set by this function.
 *
 * @param message Input message to be hashed.
 * @param[out] digest Output digest after hashing the input message.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha2_384(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA2-512 hash computation.
 *
 * The caller should allocate space for the `digest` buffer and set the `len`
 * field. If the length does not match the mode, an error message will be
 * returned. The `mode` field will be set by this function.
 *
 * @param message Input message to be hashed.
 * @param[out] digest Output digest after hashing the input message.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha2_512(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * Start a streaming SHA2 operation.
 *
 * @param hash_mode Desired mode (must be a SHA-2 mode).
 * @param[out] ctx Initialized context object.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha2_init(otcrypto_hash_mode_t hash_mode,
                                     otcrypto_sha2_context_t *ctx);

/**
 * Add more data to a streaming SHA2 operation and update the context.
 *
 * @param ctx Initialized context object (updated in place).
 * @param message Input message data.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha2_update(otcrypto_sha2_context_t *ctx,
                                       otcrypto_const_byte_buf_t message);

/**
 * Finish a streaming SHA2 operation.
 *
 * The caller should allocate space for the `digest` buffer and set the `len`
 * field. If the length does not match the context, an error message will be
 * returned. The `mode` field will be inferred from the length and set by this
 * function.
 *
 * The context data should not be used after this operation.
 *
 * @param ctx Initialized context object.
 * @param[out] digest Resulting digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha2_final(otcrypto_sha2_context_t *ctx,
                                      otcrypto_hash_digest_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA2_H_
