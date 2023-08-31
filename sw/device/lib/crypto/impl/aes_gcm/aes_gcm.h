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

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

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
 * @param tag_len Tag length in bytes
 * @param[out] tag Output buffer for tag
 * @param[out] ciphertext Output buffer for ciphertext (same length as
 * plaintext)
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_encrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t plaintext_len,
                         const uint8_t *plaintext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len, uint8_t *tag,
                         uint8_t *ciphertext);

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
 * @param tag_len Tag length in bytes
 * @param tag Authentication tag
 * @param plaintext[out] Output buffer for plaintext (same length as ciphertext)
 * @param success[out] True if authentication was successful, otherwise false
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_decrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t ciphertext_len,
                         const uint8_t *ciphertext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len,
                         const uint8_t *tag, uint8_t *plaintext,
                         hardened_bool_t *success);

/**
 * Implements the GCTR function as specified in SP800-38D, section 6.5.
 *
 * The block cipher is fixed to AES. Note that the GCTR function is a modified
 * version of the AES-CTR mode of encryption.
 *
 * Input must be less than 2^32 blocks long; that is, `len` < 2^36, since each
 * block is 16 bytes.
 *
 * @param key The AES key
 * @param icb Initial counter block, 128 bits
 * @param len Number of bytes for input and output
 * @param input Pointer to input buffer (may be NULL if `len` is 0)
 * @param[out] output Pointer to output buffer (same size as input, may be the
 * same buffer)
 */
OT_WARN_UNUSED_RESULT
status_t aes_gcm_gctr(const aes_key_t key, const aes_block_t *icb, size_t len,
                      const uint8_t *input, uint8_t *output);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_AES_GCM_H_
