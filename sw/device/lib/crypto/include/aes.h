// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * @file
 * @brief AES operations for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to denote the AES-GCM tag length.
 *
 * Values are hardened.
 */
typedef enum aead_gcm_tag_len {
  // Tag length 128 bits.
  kAeadGcmTagLen128 = 0x167,
  // Tag length 96 bits.
  kAeadGcmTagLen96 = 0x35a,
  // Tag length 64 bits.
  kAeadGcmTagLen64 = 0x5d4,
  // Tag length 32 bits.
  kAeadGcmTagLen32 = 0xf06,
} aead_gcm_tag_len_t;

/**
 * Enum to define AES mode of operation.
 *
 * Values are hardened.
 */
typedef enum block_cipher_mode {
  // AES ECB mode (electronic codebook mode).
  kBlockCipherModeEcb = 0x533,
  // AES CBC mode (cipher block chaining mode).
  kBlockCipherModeCbc = 0x45d,
  // AES CFB mode (cipher feedback mode).
  kBlockCipherModeCfb = 0xcd2,
  // AES OFB mode (output feedback mode).
  kBlockCipherModeOfb = 0x39a,
  // AES CTR mode (counter mode).
  kBlockCipherModeCtr = 0xd2c,
} block_cipher_mode_t;

/**
 * Enum to define AES operation to be performed.
 *
 * Values are hardened.
 */
typedef enum aes_operation {
  // AES operation mode encrypt.
  kAesOperationEncrypt = 0x2b6,
  // AES operation mode decrypt.
  kAesOperationDecrypt = 0x5f0,
} aes_operation_t;

/**
 * Enum to define padding scheme for AES data.
 *
 * Values are hardened.
 */
typedef enum aes_padding {
  // Pads with value same as the number of padding bytes.
  kAesPaddingPkcs7 = 0xe7f,
  // Pads with 0x80 (10000000), followed by zero bytes.
  kAesPaddingIso9797M2 = 0xfac,
  // Add no padding.
  kAesPaddingNull = 0x8ce,
} aes_padding_t;

/**
 * Context for GCM GHASH operation.
 *
 * Representation is internal to the aes-gcm ghash implementation;
 * initialize with #otcrypto_gcm_ghash_init.
 */
typedef struct gcm_ghash_context {
  // Context for the gcm-ghash operation.
  uint32_t ctx[68];
} gcm_ghash_context_t;

/**
 * Get the number of blocks needed for the plaintext length and padding mode.
 *
 * This returns the size of the padded plaintext, which is the same as the
 * ciphertext size. Returns `kCryptoStatusBadArgs` if the padding mode and
 * length are incompatible (for instance, if the padding mode is "no padding"
 * but the input length is not a multiple of the AES block size).
 *
 * @param plaintext_len Plaintext data length in bytes.
 * @param aes_padding Padding scheme to be used for the data.
 * @return Size of the padded input or ciphertext.
 * @return Result of the operation.
 */
crypto_status_t otcrypto_aes_padded_plaintext_length(size_t plaintext_len,
                                                     aes_padding_t aes_padding,
                                                     size_t *padded_len);

/**
 * Performs the AES operation.
 *
 * The input data in the `cipher_input` is first padded using the
 * `aes_padding` scheme and the output is copied to `cipher_output`.
 *
 * The caller should allocate space for the `cipher_output` buffer, which is
 * given in bytes by `otcrypto_aes_padded_plaintext_length`, and set the number
 * of bytes allocated in the `len` field of the output.  If the user-set length
 * and the expected length do not match, an error message will be returned.
 *
 * Note that, during decryption, the padding mode is ignored. This function
 * will NOT check the padding or return an error if the padding is invalid,
 * since doing so could expose a padding oracle (especially in CBC mode).
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param iv Initialization vector, used for CBC, CFB, OFB, CTR modes. May be
 *           NULL if mode is ECB.
 * @param aes_mode Required AES mode of operation.
 * @param aes_operation Required AES operation (encrypt or decrypt).
 * @param cipher_input Input data to be ciphered.
 * @param aes_padding Padding scheme to be used for the data.
 * @param[out] cipher_output Output data after cipher operation.
 * @return The result of the cipher operation.
 */
crypto_status_t otcrypto_aes(const crypto_blinded_key_t *key,
                             crypto_word32_buf_t iv,
                             block_cipher_mode_t aes_mode,
                             aes_operation_t aes_operation,
                             crypto_const_byte_buf_t cipher_input,
                             aes_padding_t aes_padding,
                             crypto_byte_buf_t cipher_output);

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
crypto_status_t otcrypto_aes_encrypt_gcm(const crypto_blinded_key_t *key,
                                         crypto_const_byte_buf_t plaintext,
                                         crypto_const_word32_buf_t iv,
                                         crypto_const_byte_buf_t aad,
                                         aead_gcm_tag_len_t tag_len,
                                         crypto_byte_buf_t *ciphertext,
                                         crypto_word32_buf_t *auth_tag);

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
crypto_status_t otcrypto_aes_decrypt_gcm(
    const crypto_blinded_key_t *key, crypto_const_byte_buf_t ciphertext,
    crypto_const_word32_buf_t iv, crypto_const_byte_buf_t aad,
    aead_gcm_tag_len_t tag_len, crypto_const_word32_buf_t auth_tag,
    crypto_byte_buf_t *plaintext, hardened_bool_t *success);

/**
 * Returns the length that the blinded key will have once wrapped.
 *
 * @param config Key configuration.
 * @param[out] wrapped_num_words Number of 32b words for the wrapped key.
 * @return Result of the operation.
 */
crypto_status_t otcrypto_aes_kwp_wrapped_len(const crypto_key_config_t config,
                                             size_t *wrapped_num_words);

/**
 * Performs the cryptographic key wrapping operation.
 *
 * This key wrap function takes an input key `key_to_wrap` and using
 * the encryption key `key_kek` outputs a wrapped key `wrapped_key`.
 *
 * The caller should allocate space for the `wrapped_key` buffer according to
 * `otcrypto_aes_kwp_wrapped_len`., and set the length of expected output
 * in the `len` field of `wrapped_key`. If the user-set length and the
 * output length do not match, an error message will be returned.
 *
 * The blinded key struct to wrap must be 32-bit aligned.
 *
 * @param key_to_wrap Pointer to the blinded key to be wrapped.
 * @param key_kek Input Pointer to the blinded encryption key.
 * @param[out] wrapped_key Pointer to the output wrapped key.
 * @return Result of the aes-kwp wrap operation.
 */
crypto_status_t otcrypto_aes_kwp_wrap(const crypto_blinded_key_t *key_to_wrap,
                                      const crypto_blinded_key_t *key_kek,
                                      crypto_word32_buf_t *wrapped_key);

/**
 * Performs the cryptographic key unwrapping operation.
 *
 * This key unwrap function takes a wrapped key `wrapped_key` and using
 * encryption key `key_kek` outputs an unwrapped key `unwrapped_key`.
 *
 * The caller must allocate space for the keyblob and set the keyblob-length
 * and keyblob fields in `unwrapped_key` accordingly. If there is not enough
 * space in the keyblob, this function will return an error. Too much space in
 * the keyblob is okay; this function will write to the first part of the
 * keyblob buffer and set the keyblob length field to the correct exact value
 * for the unwrapped key, at which point it is safe to check the new length and
 * free the remaining keyblob memory. It is always safe to allocate a keyblob
 * the same size as the wrapped key; this will always be enough space by
 * definition.
 *
 * The caller does not need to populate the blinded key configuration, since
 * this information is encrypted along with the key.  However, the caller may
 * want to check that the configuration matches expectations.
 *
 * An OK status from this function does NOT necessarily mean that unwrapping
 * succeeded; the caller must check both the returned status and the `success`
 * parameter before reading the unwrapped key.
 *
 * @param wrapped_key Pointer to the input wrapped key.
 * @param key_kek Input Pointer to the blinded encryption key.
 * @param[out] success Whether the wrapped key was valid.
 * @param[out] unwrapped_key Pointer to the output unwrapped key struct.
 * @return Result of the aes-kwp unwrap operation.
 */
crypto_status_t otcrypto_aes_kwp_unwrap(crypto_const_word32_buf_t wrapped_key,
                                        const crypto_blinded_key_t *key_kek,
                                        hardened_bool_t *success,
                                        crypto_blinded_key_t *unwrapped_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_
