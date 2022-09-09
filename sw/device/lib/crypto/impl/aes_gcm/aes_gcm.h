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

enum {
  /* Full tag size in bits. */
  kAesGcmTagNumBits = 128,
  /* Full tag size in bytes. */
  kAesGcmTagNumBytes = kAesGcmTagNumBits / 8,
  /* Full tag size in words. */
  kAesGcmTagNumWords = kAesGcmTagNumBytes / sizeof(uint32_t),
};

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
 * @param iv_len length of IV in bytes
 * @param iv IV value (may be NULL if iv_len is 0)
 * @param plaintext_len length of plaintext in bytes
 * @param plaintext plaintext value (may be NULL if plaintext_len is 0)
 * @param aad_len length of AAD in bytes
 * @param aad AAD value (may be NULL if aad_len is 0)
 * @param ciphertext Output buffer for ciphertext (same length as plaintext)
 * @param[out] tag Output buffer for tag (128 bits)
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_gcm_encrypt(const aes_key_t key, const size_t iv_len,
                            const uint8_t *iv, const size_t plaintext_len,
                            const uint8_t *plaintext, const size_t aad_len,
                            const uint8_t *aad, uint8_t *ciphertext,
                            uint8_t *tag);
/**
 * GHASH operation as defined in NIST SP800-38D, algorithm 2.
 *
 * The input size must be a multiple of the block size.
 *
 * This operation is an internal subcomponent of GCM and should not be used
 * directly except for implementing alternative, customized GCM interfaces
 * (such as using a block cipher other than AES). For other ciphers, the block
 * size must still be 128 bits.
 *
 * @param hash_subkey The hash subkey (a 128-bit cipher block).
 * @param input_len Number of bytes in the input.
 * @param input Pointer to input buffer.
 * @param[out] output Block in which to store the output.
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_gcm_ghash(const aes_block_t *hash_subkey,
                          const size_t input_len, const uint8_t *input,
                          aes_block_t *output);

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
 * (type `aes_error_t`): the return value indicates whether there was an
 * internal error while processing the function, and `success` indicates
 * whether the authentication check passed. If the return value is anything
 * other than OK, all output from this function should be discarded, including
 * `success`.
 *
 * This implementation does not support short tags.
 *
 * @param key AES key
 * @param iv_len length of IV in bytes
 * @param iv IV value (may be NULL if iv_len is 0)
 * @param ciphertext_len length of ciphertext in bytes
 * @param ciphertext plaintext value (may be NULL if ciphertext_len is 0)
 * @param aad_len length of AAD in bytes
 * @param aad AAD value (may be NULL if aad_len is 0)
 * @param tag Authentication tag (128 bits)
 * @param plaintext[out] Output buffer for plaintext (same length as ciphertext)
 * @param success[out] True if authentication was successful, otherwise false
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_gcm_decrypt(const aes_key_t key, const size_t iv_len,
                            const uint8_t *iv, const size_t ciphertext_len,
                            const uint8_t *ciphertext, const size_t aad_len,
                            const uint8_t *aad, const uint8_t *tag,
                            uint8_t *plaintext, hardened_bool_t *success);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_AES_GCM_H_
