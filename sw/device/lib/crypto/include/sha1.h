// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA1_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA1_H_

#include "datatypes.h"

/**
 * @file
 * @brief SHA-1 and HMAC-SHA-1 operations for the OpenTitan cryptography
 * library.
 *
 * NOTE: SHA-1 and HMAC-SHA-1 are implemented in plain software (without
 * hardware acceleration) for legacy compatibility and are NOT hardened against
 * fault injection (FI) or side-channel analysis (SCA).
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of an opaque SHA-1 streaming context in 32-bit words.
   */
  kOtcryptoSha1CtxStructWords = 24,
  /**
   * Size of an opaque HMAC-SHA-1 streaming context in 32-bit words.
   */
  kOtcryptoHmacSha1CtxStructWords = 40,
};

/**
 * Opaque SHA-1 hash context.
 *
 * Representation is internal to the hash implementation; initialize with
 * #otcrypto_sha1_init.
 */
typedef struct otcrypto_sha1_context {
  uint32_t data[kOtcryptoSha1CtxStructWords];
} otcrypto_sha1_context_t;

/**
 * Opaque HMAC-SHA-1 context.
 *
 * Representation is internal to the HMAC implementation; initialize with
 * #otcrypto_hmac_sha1_init.
 */
typedef struct otcrypto_hmac_sha1_context {
  uint32_t data[kOtcryptoHmacSha1CtxStructWords];
} otcrypto_hmac_sha1_context_t;

/**
 * One-shot SHA-1 hash computation.
 *
 * Note: This is a plain software implementation of SHA-1 and is NOT hardened
 * against fault injection (FI) or side-channel analysis (SCA).
 *
 * The caller should allocate space for the `digest` buffer (5 32-bit words /
 * 20 bytes) and set the `len` field to 5. The `mode` field will be populated
 * by this function (`kOtcryptoHashModeSha1`).
 *
 * @param message Input message to be hashed.
 * @param[out] digest Output digest after hashing the input message.
 * @return Result of the hash operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha1(const otcrypto_const_byte_buf_t *message,
                                otcrypto_hash_digest_t *digest);

/**
 * Initialize a context for a streaming SHA-1 computation.
 *
 * Note: This is a plain software implementation of SHA-1 and is NOT hardened
 * against fault injection (FI) or side-channel analysis (SCA).
 *
 * Initializes `ctx` for a SHA-1 computation.
 *
 * @param[out] ctx Uninitialized context object to be populated.
 * @return Result of the hash init operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha1_init(otcrypto_sha1_context_t *ctx);

/**
 * Update a context for a streaming SHA-1 computation.
 *
 * Note: This is a plain software implementation of SHA-1 and is NOT hardened
 * against fault injection (FI) or side-channel analysis (SCA).
 *
 * Appends `input_message` to the hash computation represented by `ctx` and
 * updates `ctx` to represent the new state.
 *
 * @param ctx Context object from #otcrypto_sha1_init.
 * @param input_message Next chunk of input message to be hashed.
 * @return Result of the hash update operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha1_update(
    otcrypto_sha1_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message);

/**
 * Finalize a context for a streaming SHA-1 computation.
 *
 * Note: This is a plain software implementation of SHA-1 and is NOT hardened
 * against fault injection (FI) or side-channel analysis (SCA).
 *
 * Computes the final digest from the hash computation represented by `ctx`.
 *
 * The caller should allocate space for the `digest` buffer (5 32-bit words /
 * 20 bytes) and set the `len` field to 5. This function will populate the
 * `mode` field (`kOtcryptoHashModeSha1`).
 *
 * @param ctx Context object from #otcrypto_sha1_init.
 * @param[out] digest Output digest after hashing the input message.
 * @return Result of the hash final operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha1_final(otcrypto_sha1_context_t *ctx,
                                      otcrypto_hash_digest_t *digest);

/**
 * Performs the HMAC-SHA-1 function on the input data.
 *
 * Note: This is a plain software implementation of HMAC-SHA-1 and is NOT
 * hardened against fault injection (FI) or side-channel analysis (SCA). Any
 * `security_level` in `key->config` is accepted for API compatibility, but no
 * hardware or software SCA/FI countermeasures are applied.
 *
 * The caller should allocate 20 bytes (5 32-bit words) of space for the `tag`
 * buffer and set its `len` field to 5.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param[out] tag Output authentication tag.
 * @return The result of the HMAC-SHA-1 operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_sha1(
    const otcrypto_blinded_key_t *key,
    const otcrypto_const_byte_buf_t *input_message, otcrypto_word32_buf_t *tag);

/**
 * Initializes a streaming HMAC-SHA-1 operation.
 *
 * Note: This is a plain software implementation of HMAC-SHA-1 and is NOT
 * hardened against fault injection (FI) or side-channel analysis (SCA). Any
 * `security_level` in `key->config` is accepted for API compatibility, but no
 * hardware or software SCA/FI countermeasures are applied.
 *
 * @param[out] ctx Context object for the streaming operation.
 * @param key Pointer to the blinded key struct with key shares.
 * @return Result of the HMAC-SHA-1 init operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_sha1_init(otcrypto_hmac_sha1_context_t *ctx,
                                          const otcrypto_blinded_key_t *key);

/**
 * Updates a streaming HMAC-SHA-1 operation with additional message data.
 *
 * Note: This is a plain software implementation of HMAC-SHA-1 and is NOT
 * hardened against fault injection (FI) or side-channel analysis (SCA).
 *
 * @param ctx Context object for the streaming operation.
 * @param input_message Input message chunk to be processed.
 * @return Result of the HMAC-SHA-1 update operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_sha1_update(
    otcrypto_hmac_sha1_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message);

/**
 * Finalizes a streaming HMAC-SHA-1 operation and produces the tag.
 *
 * Note: This is a plain software implementation of HMAC-SHA-1 and is NOT
 * hardened against fault injection (FI) or side-channel analysis (SCA).
 *
 * The caller should allocate 20 bytes (5 32-bit words) of space for the `tag`
 * buffer and set its `len` field to 5.
 *
 * @param ctx Context object for the streaming operation.
 * @param[out] tag Output authentication tag.
 * @return Result of the HMAC-SHA-1 final operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hmac_sha1_final(otcrypto_hmac_sha1_context_t *ctx,
                                           otcrypto_word32_buf_t *tag);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA1_H_
