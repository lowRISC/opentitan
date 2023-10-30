// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_AES_GCM_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_AES_GCM_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Stage of a streaming AES-GCM operation.
 */
typedef enum aes_gcm_state {
  kAesGcmStateUpdateAad,
  kAesGcmStateUpdateEncryptedData,
} aes_gcm_state_t;

/**
 * AES-GCM context object for streaming operations.
 */
typedef struct aes_gcm_context {
  /**
   * State of the ongoing operation.
   */
  aes_gcm_state_t state;
  /**
   * Whether this is an encryption operation (false indicates decryption).
   */
  hardened_bool_t is_encrypt;
  /**
   * Underlying AES-CTR key.
   */
  aes_key_t key;
  /**
   * Initial counter block (J0 in the spec).
   */
  aes_block_t initial_counter_block;
  /**
   * Current counter block for the main GCTR operation over the plaintext.
   */
  aes_block_t gctr_iv;
  /**
   * Length of the associated data received so far, in bytes.
   */
  size_t aad_len;
  /**
   * Length of the input so far, in bytes.
   */
  size_t input_len;
  /**
   * Partial GHASH block.
   *
   * Length is always equal to `aad_len % kGhashBlockNumBytes` if the state is
   * `kAesGcmStateUpdateAad`, and is always 0 if the state
   * is `kAesGcmStateUpdateEncryptedData` (since ciphertext gets accumulated in
   * full-block increments). The block may be empty, but will never be full.
   */
  ghash_block_t partial_ghash_block;
  /**
   * Partial input block.
   *
   * Length is always equal to `input_len % kAesBlockNumBytes`; the block may
   * be empty, but will never be full.
   */
  aes_block_t partial_aes_block;
  /**
   * Current context for the tag's ongoing GHASH computation.
   */
  ghash_context_t ghash_ctx;
} aes_gcm_context_t;

/**
 * AES-GCM authenticated encryption as defined in NIST SP800-38D, algorithm 4.
 *
 * The key is represented as two shares which are XORed together to get the
 * real key value. The IV must be either 96 or 128 bits.
 *
 * The byte-lengths of the plaintext and AAD must each be < 2^32. This is a
 * tighter constraint than the length limits in section 5.2.1.1.
 *
 * This implementation does not support short tags.
 *
 * @param key AES key
 * @param iv_len length of IV in 32-bit words
 * @param iv IV value (may be NULL if iv_len is 0)
 * @param plaintext_len length of plaintext in bytes
 * @param plaintext plaintext value (may be NULL if plaintext_len is 0)
 * @param aad_len length of AAD in bytes
 * @param aad AAD value (may be NULL if aad_len is 0)
 * @param tag_len Tag length in 32-bit words
 * @param[out] tag Output buffer for tag
 * @param[out] ciphertext Output buffer for ciphertext (same length as
 * plaintext)
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t plaintext_len,
                         const uint8_t *plaintext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len,
                         uint32_t *tag, uint8_t *ciphertext);

/**
 * AES-GCM authenticated decryption as defined in NIST SP800-38D, algorithm 5.
 *
 * The key is represented as two shares which are XORed together to get the
 * real key value. The IV must be either 96 or 128 bits.
 *
 * The byte-lengths of the plaintext and AAD must each be < 2^32. This is a
 * tighter constraint than the length limits in section 5.2.1.1.
 *
 * If authentication fails, this function will return `kHardenedBoolFalse` for
 * the `success` output parameter, and the plaintext should be ignored. Note
 * the distinction between the `success` output parameter and the return value
 * (type `status_t`): the return value indicates whether there was an
 * internal error while processing the function, and `success` indicates
 * whether the authentication check passed. If the return value is anything
 * other than OK, all output from this function should be discarded, including
 * `success`.
 *
 * @param key AES key
 * @param iv_len length of IV in 32-bit words
 * @param iv IV value (may be NULL if iv_len is 0)
 * @param ciphertext_len length of ciphertext in bytes
 * @param ciphertext plaintext value (may be NULL if ciphertext_len is 0)
 * @param aad_len length of AAD in bytes
 * @param aad AAD value (may be NULL if aad_len is 0)
 * @param tag_len Tag length in 32-bit words
 * @param tag Authentication tag
 * @param[out] plaintext Output buffer for plaintext (same length as ciphertext)
 * @param[out] success True if authentication was successful, otherwise false
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t ciphertext_len,
                         const uint8_t *ciphertext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len,
                         const uint32_t *tag, uint8_t *plaintext,
                         hardened_bool_t *success);

/**
 * Starts an AES-GCM authenticated encryption operation.
 *
 * Populates the `ctx` parameter with initial values.
 *
 * Typical usage looks like this (the `update_encrypted_data` and `update_aad`
 * calls cannot be interleaved with each other; you must pass all the
 * associated data before adding encrypted data):
 *   aes_gcm_encrypt_init(...)
 *   aes_gcm_update_aad(...) // call 0 or more times
 *   aes_gcm_update_encrypted_data(...) // call 0 or more times
 *   aes_gcm_encrypt_final(...)
 *
 * @param key AES key
 * @param iv_len length of IV in 32-bit words
 * @param iv IV value (may be NULL if iv_len is 0)
 * @param[out] ctx AES-GCM context object.
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt_init(const aes_key_t key, const size_t iv_len,
                              const uint32_t *iv, aes_gcm_context_t *ctx);

/**
 * Updates the associated data for an AES-GCM operation.
 *
 * @param ctx AES-GCM context object.
 * @param aad_len length of aad in bytes
 * @param aad aad value (may be NULL if aad_len is 0)
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_update_aad(aes_gcm_context_t *ctx, const size_t aad_len,
                            const uint8_t *aad);

/**
 * Updates the encrypted input for an AES-GCM operation.
 *
 * For encryption, this updates the plaintext. For decryption, it updates the
 * ciphertext.
 *
 * Updates the context and returns output that corresponds to (full blocks
 * of) the new chunk of input. The output buffer must have enough space to
 * hold all full blocks that could be produced; rounding the input length up
 * to the next full block is always enough, but if there is definitely no
 * partial data present then it is acceptable to round down. The output
 * buffer may be NULL if `input_len` is 0.
 *
 * Returns the number of output bytes written in `output_len`.
 *
 * @param ctx AES-GCM context object.
 * @param input_len length of input in bytes
 * @param input input value (may be NULL if input_len is 0)
 * @param[out] output_len number of output bytes written
 * @param[out] output resulting output data
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_update_encrypted_data(aes_gcm_context_t *ctx,
                                       const size_t input_len,
                                       const uint8_t *input, size_t *output_len,
                                       uint8_t *output);

/**
 * Finishes an AES-GCM encryption operation.
 *
 * Finishes processing the data and computes the tag. If there is partial data
 * present, `output` must have at least `kAesBlockNumBytes` bytes of space
 * available. If there is definitely no partial data present, `output` will be
 * unused and may be NULL.
 *
 * Returns the number of output bytes written in `output_len`.
 *
 * @param ctx AES-GCM context object.
 * @param tag_len Tag length in 32-bit words
 * @param[out] tag Output buffer for tag
 * @param[out] output_len number of output bytes written
 * @param[out] output resulting output data
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt_final(aes_gcm_context_t *ctx, size_t tag_len,
                               uint32_t *tag, size_t *output_len,
                               uint8_t *output);

/**
 * Starts an AES-GCM authenticated decryption operation.
 *
 * Populates the `ctx` parameter with initial values.
 *
 * Typical usage looks like this (the `update_encrypted_data` and `update_aad`
 * calls cannot be interleaved with each other; you must pass all the
 * associated data before adding encrypted data):
 *   aes_gcm_decrypt_init(...)
 *   aes_gcm_update_aad(...) // call 0 or more times
 *   aes_gcm_update_encrypted_data(...) // call 0 or more times
 *   aes_gcm_encrypt_final(...)
 *
 * @param key AES key
 * @param iv_len length of IV in 32-bit words
 * @param iv IV value (may be NULL if iv_len is 0)
 * @param[out] ctx AES-GCM context object.
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt_init(const aes_key_t key, const size_t iv_len,
                              const uint32_t *iv, aes_gcm_context_t *ctx);

/**
 * Finishes an AES-GCM decryption operation.
 *
 * Finishes processing the data and computes the tag, then compares it to the
 * actual tag. If there is partial data present, `output` must have at least
 * `kAesBlockNumBytes` bytes of space available. If there is definitely no
 * partial data present, `output` will be unused and may be NULL.
 *
 * Returns the number of output bytes written in `output_len`.
 *
 * If authentication fails, this function will return `kHardenedBoolFalse` for
 * the `success` output parameter, and the plaintext should be ignored. Note
 * the distinction between the `success` output parameter and the return value
 * (type `status_t`): the return value indicates whether there was an
 * internal error while processing the function, and `success` indicates
 * whether the authentication check passed. If the return value is anything
 * other than OK, all output from this function should be discarded, including
 * `success`.
 *
 * @param ctx AES-GCM context object.
 * @param tag_len Tag length in 32-bit words
 * @param[out] tag Output buffer for tag
 * @param[out] output_len number of output bytes written
 * @param[out] output resulting output data
 * @param[out] success True if authentication was successful, otherwise false
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt_final(aes_gcm_context_t *ctx, size_t tag_len,
                               const uint32_t *tag, size_t *output_len,
                               uint8_t *output, hardened_bool_t *success);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_AES_GCM_H_
