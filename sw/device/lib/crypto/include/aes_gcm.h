// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_GCM_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_GCM_H_

#include "datatypes.h"

/**
 * @file
 * @brief AES-GCM operations for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to denote the AES-GCM tag length.
 *
 * Values are hardened.
 */
typedef enum otcrypto_aes_gcm_tag_len {
  // Tag length 128 bits.
  kOtcryptoAesGcmTagLen128 = 0x167,
  // Tag length 96 bits.
  kOtcryptoAesGcmTagLen96 = 0x35a,
  // Tag length 64 bits.
  kOtcryptoAesGcmTagLen64 = 0x5d4,
  // Tag length 32 bits.
  kOtcryptoAesGcmTagLen32 = 0xf06,
} otcrypto_aes_gcm_tag_len_t;

/**
 * Context for a streaming AES-GCM operation.
 *
 * Representation is internal to the AES-GCM implementation and subject to
 * change.
 */
typedef struct otcrypto_aes_gcm_context {
  uint32_t data[98];
} otcrypto_aes_gcm_context_t;

/**
 * Performs the AES-GCM authenticated encryption operation.
 *
 * This function encrypts the input `plaintext` to produce an
 * output `ciphertext`. Together it generates an authentication
 * tag `auth_tag` on the ciphered data and any non-confidential
 * additional authenticated data `aad`.
 *
 * The caller should allocate space for the `ciphertext` buffer,
 * (same length as input), `auth_tag` buffer (same as tag_len), and
 * set the length of expected outputs in the `len` field of
 * `ciphertext` and `auth_tag`. If the user-set length and the output
 * length does not match, an error message will be returned.
 *
 * @param key Pointer to the blinded gcm-key struct.
 * @param plaintext Input data to be encrypted and authenticated.
 * @param iv Initialization vector for the encryption function.
 * @param aad Additional authenticated data.
 * @param tag_len Length of authentication tag to be generated.
 * @param[out] ciphertext Encrypted output data, same length as input data.
 * @param[out] auth_tag Generated authentication tag.
 * @return Result of the authenticated encryption.
 * operation
 */
otcrypto_status_t otcrypto_aes_gcm_encrypt(otcrypto_blinded_key_t *key,
                                           otcrypto_const_byte_buf_t plaintext,
                                           otcrypto_const_word32_buf_t iv,
                                           otcrypto_const_byte_buf_t aad,
                                           otcrypto_aes_gcm_tag_len_t tag_len,
                                           otcrypto_byte_buf_t ciphertext,
                                           otcrypto_word32_buf_t auth_tag);

/**
 * Performs the AES-GCM authenticated decryption operation.
 *
 * This function first verifies if the authentication tag `auth_tag`
 * matches the internally generated tag. Upon verification, the
 * function decrypts the input `ciphertext` to get a `plaintext data.
 *
 * The caller should allocate space for the `plaintext` buffer,
 * (same length as ciphertext), and set the length of expected output
 * in the `len` field of `plaintext`. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * The caller must check the `success` argument before operating on
 * `plaintext`. If the authentication check fails, then `plaintext` should not
 * be used and there are no guarantees about its contents.
 *
 * @param key Pointer to the blinded gcm-key struct.
 * @param ciphertext Input data to be decrypted.
 * @param iv Initialization vector for the decryption function.
 * @param aad Additional authenticated data.
 * @param tag_len Length of authentication tag to be generated.
 * @param auth_tag Authentication tag to be verified.
 * @param[out] plaintext Decrypted plaintext data, same len as input data.
 * @param[out] success True if the authentication check passed, otherwise false.
 * @return Result of the authenticated decryption.
 * operation
 */
otcrypto_status_t otcrypto_aes_gcm_decrypt(
    otcrypto_blinded_key_t *key, otcrypto_const_byte_buf_t ciphertext,
    otcrypto_const_word32_buf_t iv, otcrypto_const_byte_buf_t aad,
    otcrypto_aes_gcm_tag_len_t tag_len, otcrypto_const_word32_buf_t auth_tag,
    otcrypto_byte_buf_t plaintext, hardened_bool_t *success);

/**
 * Initializes the AES-GCM authenticated encryption operation.
 *
 * The order of operations for encryption is:
 *   - `otcrypto_aes_gcm_encrypt_init()` called once
 *   - `otcrypto_aes_gcm_update_aad()` called zero or more times
 *   - `otcrypto_aes_gcm_update_encrypted_data()` called zero or more times
 *   - `otcrypto_aes_gcm_encrypt_final()` called once
 *
 * Associated data must be added first, before encrypted data; the caller may
 * not call `otcrypto_aes_gcm_udpate_aad()` after the first call to
 * `otcrypto_aes_gcm_update_encrypted_data()`.
 *
 * The resulting AES-GCM context will include pointers into the keyblob of the
 * blinded key. It is important that the blinded key (or at least the keyblob)
 * remains live as long as `ctx` is. The IV is safe to free.
 *
 * @param key Pointer to the blinded key struct.
 * @param iv Initialization vector for the encryption function.
 * @param[out] ctx Context object for the operation.
 * @return Result of the initialization operation.
 */
otcrypto_status_t otcrypto_aes_gcm_encrypt_init(
    otcrypto_blinded_key_t *key, otcrypto_const_word32_buf_t iv,
    otcrypto_aes_gcm_context_t *ctx);

/**
 * Initializes the AES-GCM authenticated decryption operation.
 *
 * The order of operations for decryption is:
 *   - `otcrypto_aes_gcm_decrypt_init()` called once
 *   - `otcrypto_aes_gcm_update_aad()` called zero or more times
 *   - `otcrypto_aes_gcm_update_encrypted_data()` called zero or more times
 *   - `otcrypto_aes_gcm_decrypt_final()` called once
 *
 * Associated data must be added first, before encrypted data; the caller may
 * not call `otcrypto_aes_gcm_udpate_aad()` after the first call to
 * `otcrypto_aes_gcm_update_encrypted_data()`.
 *
 * The resulting AES-GCM context will include pointers into the keyblob of the
 * blinded key. It is important that the blinded key (or at least the keyblob)
 * remains live as long as `ctx` is. The IV is safe to free.
 *
 * IMPORTANT: Although this routine produces decrypted data incrementally, it
 * is the caller's responsibility to ensure that they do not trust the
 * decrypted data until the tag check passes.
 *
 * @param key Pointer to the blinded key struct.
 * @param iv Initialization vector for the decryption function.
 * @param[out] ctx Context object for the operation.
 * @return Result of the initialization operation.
 */
otcrypto_status_t otcrypto_aes_gcm_decrypt_init(
    otcrypto_blinded_key_t *key, otcrypto_const_word32_buf_t iv,
    otcrypto_aes_gcm_context_t *ctx);
/**
 * Updates additional authenticated data for an AES-GCM operation.
 *
 * May be used for either encryption or decryption. Call
 * `otcrypto_aes_gcm_encrypt_init` or `otcrypto_aes_gcm_decrypt_init` first.
 *
 * @param ctx Context object for the operation, updated in place.
 * @param aad Additional authenticated data.
 * @return Result of the update operation.
 */
otcrypto_status_t otcrypto_aes_gcm_update_aad(otcrypto_aes_gcm_context_t *ctx,
                                              otcrypto_const_byte_buf_t aad);

/**
 * Updates authenticated-and-encrypted data for an AES-GCM operation.
 *
 * May be used for either encryption or decryption. Call
 * `otcrypto_aes_gcm_encrypt_init` or `otcrypto_aes_gcm_decrypt_init` first.
 *
 * The caller should allocate space for the output and set the `len` field
 * accordingly.
 *
 * For encryption, `input` is the plaintext and `output` is the ciphertext; for
 * decryption, they are reversed. The output must always be long enough to
 * store all full 128-bit blocks of encrypted data received so far minus all
 * output produced so far; rounding the input length to the next 128-bit
 * boundary is always enough, but if the caller knows the exact byte-length of
 * input so far they can calculate it exactly. Returns an error if `output` is
 * not long enough; if `output` is overly long, only the first
 * `output_bytes_written` bytes will be used.
 *
 * @param ctx Context object for the operation, updated in place.
 * @param input Plaintext for encryption, ciphertext for decryption.
 * @param[out] output Ciphertext for encryption, plaintext for decryption.
 * @param[out] output_bytes_written Number of bytes written to `output`.
 * @return Result of the update operation.
 */
otcrypto_status_t otcrypto_aes_gcm_update_encrypted_data(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_const_byte_buf_t input,
    otcrypto_byte_buf_t output, size_t *output_bytes_written);

/**
 * Finishes the AES-GCM authenticated encryption operation.
 *
 * Processes any remaining plaintext from the context and computes the
 * authentication tag and up to 1 block of ciphertext.
 *
 * The caller should allocate space for the ciphertext and tag buffers and set
 * the `len` fields accordingly. This function returns the
 * `ciphertext_bytes_written` parameter with the number of bytes written to
 * `ciphertext`, which is always either 16 or 0. This function returns an error
 * if the ciphertext or tag buffer is not long enough.
 *
 * @param ctx Context object for the operation.
 * @param tag_len Length of authentication tag to be generated.
 * @param[out] ciphertext Encrypted output data.
 * @param[out] ciphertext_bytes_written Number of bytes written to `ciphertext`.
 * @param[out] auth_tag Generated authentication tag.
 * @return Result of the final operation.
 */
otcrypto_status_t otcrypto_aes_gcm_encrypt_final(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_aes_gcm_tag_len_t tag_len,
    otcrypto_byte_buf_t ciphertext, size_t *ciphertext_bytes_written,
    otcrypto_word32_buf_t auth_tag);

/**
 * Finishes the AES-GCM authenticated decryption operation.
 *
 * Processes any remaining ciphertext from the context and computes the
 * authentication tag and up to 1 block of plaintext.
 *
 * The caller should allocate space for the plaintext buffer and set the `len`
 * field accordingly. This function returns the `ciphertext_bytes_written`
 * parameter with the number of bytes written to `ciphertext`. This function
 * returns an error if the plaintext buffer is not long enough.
 *
 * IMPORTANT: the caller must check both the returned status and the `success`
 * parameter to know if the tag is valid. The returned status may be OK even if
 * the tag check did not succeed, if there were no errors during processing.
 *
 * @param ctx Context object for the operation.
 * @param auth_tag Authentication tag to check.
 * @param tag_len Length of authentication tag.
 * @param[out] plaintext Decrypted output data.
 * @param[out] plaintext_bytes_written Number of bytes written to `plaintext`.
 * @param[out] success Whether the tag passed verification.
 * @return Result of the final operation.
 */
otcrypto_status_t otcrypto_aes_gcm_decrypt_final(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_const_word32_buf_t auth_tag,
    otcrypto_aes_gcm_tag_len_t tag_len, otcrypto_byte_buf_t plaintext,
    size_t *plaintext_bytes_written, hardened_bool_t *success);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_GCM_H_
