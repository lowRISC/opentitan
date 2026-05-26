// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * AES-GCM context object for streaming operations.
 */
typedef struct aes_gcm_context {
  /**
   * Whether this is an encryption operation (false indicates decryption).
   */
  hardened_bool_t is_encrypt;
  /**
   * Underlying AES-CTR key.
   */
  aes_key_t key;
  /**
   * Security level of the underlying AES-CTR key.
   */
  otcrypto_key_security_level_t security_level;
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
} __attribute__((aligned(sizeof(uint32_t)))) aes_gcm_context_t;

/**
 * AES-GCM authenticated encryption as defined in NIST SP800-38D, algorithm 4.
 *
 * The key is represented as two shares which are XORed together to get the
 * real key value. The IV must be either 96 or 128 bits.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
 *
 * The byte-lengths of the plaintext and AAD must each be < 2^32. This is a
 * tighter constraint than the length limits in section 5.2.1.1.
 *
 * This implementation does not support short tags.
 *
 * @param key AES key
 * @param iv IV buffer (data may be NULL if len is 0)
 * @param plaintext plaintext buffer (data may be NULL if len is 0)
 * @param aad AAD buffer (data may be NULL if len is 0)
 * @param security_level The used security level
 * @param[out] tag Output buffer for tag (len is used as input for the tag
 * length)
 * @param[out] ciphertext Output buffer for ciphertext (same length as
 * plaintext)
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt(const aes_key_t key,
                         const otcrypto_const_word32_buf_t *iv,
                         const otcrypto_const_byte_buf_t *plaintext,
                         const otcrypto_const_byte_buf_t *aad,
                         otcrypto_word32_buf_t *tag,
                         otcrypto_key_security_level_t security_level,
                         otcrypto_byte_buf_t *ciphertext);

/**
 * AES-GCM authenticated decryption as defined in NIST SP800-38D, algorithm 5.
 *
 * The key is represented as two shares which are XORed together to get the
 * real key value. The IV must be either 96 or 128 bits.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
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
 * @param iv IV buffer (data may be NULL if len is 0)
 * @param ciphertext ciphertext buffer (data may be NULL if len is 0)
 * @param aad AAD buffer (data may be NULL if len is 0)
 * @param tag Authentication tag buffer
 * @param security_level The used security level
 * @param[out] plaintext Output buffer for plaintext (same length as ciphertext)
 * @param[out] success True if authentication was successful, otherwise false
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt(const aes_key_t key,
                         const otcrypto_const_word32_buf_t *iv,
                         const otcrypto_const_byte_buf_t *ciphertext,
                         const otcrypto_const_byte_buf_t *aad,
                         const otcrypto_const_word32_buf_t *tag,
                         otcrypto_byte_buf_t *plaintext,
                         otcrypto_key_security_level_t security_level,
                         hardened_bool_t *success);

/**
 * Starts an AES-GCM authenticated encryption operation.
 *
 * Populates the `ctx` parameter with initial values.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
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
 * @param iv IV buffer (data may be NULL if len is 0)
 * @param[out] ctx AES-GCM context object.
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt_init(const aes_key_t key,
                              const otcrypto_const_word32_buf_t *iv,
                              aes_gcm_context_t *ctx);

/**
 * Updates the associated data for an AES-GCM operation.
 *
 * @param ctx AES-GCM context object.
 * @param aad aad vuffer (data may be NULL if len is 0)
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_update_aad(aes_gcm_context_t *ctx,
                            const otcrypto_const_byte_buf_t *aad);

/**
 * Updates the encrypted input for an AES-GCM operation.
 *
 * For encryption, this updates the plaintext. For decryption, it updates the
 * ciphertext.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
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
 * @param input input buffer (data may be NULL if len is 0)
 * @param[out] output resulting output data buffer
 * @param[out] bytes_written number of output bytes written
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_update_encrypted_data(aes_gcm_context_t *ctx,
                                       const otcrypto_const_byte_buf_t *input,
                                       otcrypto_byte_buf_t *output,
                                       size_t *bytes_written);

/**
 * Finishes an AES-GCM encryption operation.
 *
 * Finishes processing the data and computes the tag. If there is partial data
 * present, `output` must have at least `kAesBlockNumBytes` bytes of space
 * available. If there is definitely no partial data present, `output` will be
 * unused and may be NULL.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
 *
 * Returns the number of output bytes written in `output_len`.
 *
 * @param ctx AES-GCM context object.
 * @param[out] tag Output buffer for tag (len used as input)
 * @param[out] output resulting output data buffer
 * @param[out] bytes_written number of output bytes written
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt_final(aes_gcm_context_t *ctx,
                               otcrypto_word32_buf_t *tag,
                               otcrypto_byte_buf_t *output,
                               size_t *bytes_written);

/**
 * Starts an AES-GCM authenticated decryption operation.
 *
 * Populates the `ctx` parameter with initial values.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
 *
 * Typical usage looks like this (the `update_encrypted_data` and `update_aad`
 * calls cannot be interleaved with each other; you must pass all the
 * associated data before adding encrypted data):
 *   aes_gcm_decrypt_init(...)
 *   aes_gcm_update_aad(...) // call 0 or more times
 *   aes_gcm_update_encrypted_data(...) // call 0 or more times
 *   aes_gcm_decrypt_final(...)
 *
 * @param key AES key
 * @param iv IV buffer (data may be NULL if len is 0)
 * @param[out] ctx AES-GCM context object.
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt_init(const aes_key_t key,
                              const otcrypto_const_word32_buf_t *iv,
                              aes_gcm_context_t *ctx);

/**
 * Finishes an AES-GCM decryption operation.
 *
 * If the key is a sideloaded key, it is the caller's responsibility to load
 * and clear it.
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
 * @param[out] tag Output buffer for tag (len used for input)
 * @param[out] output resulting output data buffer
 * @param[out] bytes_written number of output bytes written
 * @param[out] success True if authentication was successful, otherwise false
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt_final(aes_gcm_context_t *ctx,
                               const otcrypto_const_word32_buf_t *tag,
                               otcrypto_byte_buf_t *output,
                               size_t *bytes_written, hardened_bool_t *success);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_AES_GCM_H_
