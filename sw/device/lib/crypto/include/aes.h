// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_

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
  kAeadGcmTagLen128 = 0xb9ab,
  // Tag length 120 bits.
  kAeadGcmTagLen120 = 0xae53,
  // Tag length 112 bits.
  kAeadGcmTagLen112 = 0x175d,
  // Tag length 104 bits.
  kAeadGcmTagLen104 = 0x68fc,
  // Tag length 96 bits.
  kAeadGcmTagLen96 = 0x7686,
  // Tag length 64 bits.
  kAeadGcmTagLen64 = 0xc6a9,
  // Tag length 32 bits.
  kAeadGcmTagLen32 = 0x4b37,
} aead_gcm_tag_len_t;

/**
 * Enum to define AES mode of operation.
 *
 * Values are hardened.
 */
typedef enum block_cipher_mode {
  // AES ECB mode (electronic codebook mode).
  kBlockCipherModeEcb = 0x7cae,
  // AES CBC mode (cipher block chaining mode).
  kBlockCipherModeCbc = 0x9736,
  // AES CFB mode (cipher feedback mode).
  kBlockCipherModeCfb = 0xe378,
  // AES OFB mode (output feedback mode).
  kBlockCipherModeOfb = 0x9cdd,
  // AES CTR mode (counter mode).
  kBlockCipherModeCtr = 0x4a1f,
} block_cipher_mode_t;

/**
 * Enum to define AES operation to be performed.
 *
 * Values are hardened.
 */
typedef enum aes_operation {
  // AES operation mode encrypt.
  kAesOperationEncrypt = 0xdea9,
  // AES operation mode decrypt.
  kAesOperationDecrypt = 0x5d5a,
} aes_operation_t;

/**
 * Enum to define padding scheme for AES data.
 *
 * Values are hardened.
 */
typedef enum aes_padding {
  // Pads with value same as the number of padding bytes.
  kAesPaddingPkcs7 = 0xce99,
  // Pads with 0x80 (10000000), followed by zero bytes.
  kAesPaddingIso9797M2 = 0xb377,
  // Pads with 0x00 bytes.
  kAesPaddingIso9797M1 = 0x49eb,
  // Pads with random bytes, last byte is no. of padded bytes.
  kAesPaddingRandom = 0x746c,
  // Pads with 0x00 bytes, last byte is no. of padded bytes.
  kAesPaddingX923 = 0xed32,
  // Add no padding.
  kAesPaddingNull = 0x259f,
} aes_padding_t;

/**
 * Context for GCM GHASH operation.
 *
 * Representation is internal to the hmac implementation; initialize
 * with #otcrypto_gcm_ghash_init.
 */
typedef struct gcm_ghash_context gcm_ghash_context_t;

/**
 * Performs the AES initialization operation.
 *
 * The `aes_mode` and `aes_operation` are selected and the `key`, `iv`
 * are loaded into the register.
 *
 * @param key Pointer to the blinded key struct with key shares
 * @param iv Initialization vector, used for CBC, CFB, OFB, CTR modes
 * @param aes_mode Required AES mode of operation
 * @param aes_operation Required AES operation (encrypt or decrypt)
 * @return The result of the init operation
 */
crypto_status_t otcrypto_aes_init(const crypto_blinded_key_t *key,
                                  crypto_uint8_buf_t iv,
                                  block_cipher_mode_t aes_mode,
                                  aes_operation_t aes_operation);

/**
 * Performs the AES cipher operation.
 *
 * The #otcrypto_aes_init should be called before this function,
 * to initialize the key, AES mode and AES cipher operation.
 *
 * The input data in the `cipher_input` is first padded using the
 * `aes_padding` scheme and the output is copied to `cipher_output`.
 *
 * The caller should allocate space for the `cipher_output` buffer,
 * (same length as input), and set the length of expected output in
 * the `len` field of the output. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * @param cipher_input Input data to be ciphered
 * @param aes_padding Padding scheme to be used for the data
 * @param cipher_output Output data after cipher operation
 * @return The result of the cipher operation
 */
crypto_status_t otcrypto_aes_cipher(crypto_const_uint8_buf_t cipher_input,
                                    aes_padding_t aes_padding,
                                    crypto_uint8_buf_t *cipher_output);

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
 * @param key Pointer to the blinded gcm-key struct
 * @param plaintext Input data to be encrypted and authenticated
 * @param iv Initialization vector for the encryption function
 * @param aad Additional authenticated data
 * @param tag_len Length of authentication tag to be generated
 * @param ciphertext Encrypted output data, same length as input data
 * @param auth_tag Generated authentication tag
 * @return Result of the authenticated encryption
 * operation
 */
crypto_status_t otcrypto_aes_encrypt_gcm(
    const crypto_blinded_key_t *key, crypto_const_uint8_buf_t plaintext,
    crypto_uint8_buf_t iv, crypto_uint8_buf_t aad, aead_gcm_tag_len_t tag_len,
    crypto_uint8_buf_t *ciphertext, crypto_uint8_buf_t *auth_tag);

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
 * @param key Pointer to the blinded gcm-key struct
 * @param ciphertext Input data to be decrypted
 * @param iv Initialization vector for the decryption function
 * @param aad Additional authenticated data
 * @param auth_tag Authentication tag to be verified
 * @param plaintext Decrypted plaintext data, same len as input data
 * @return Result of the authenticated decryption
 * operation
 */
crypto_status_t otcrypto_aes_decrypt_gcm(const crypto_blinded_key_t *key,
                                         crypto_const_uint8_buf_t ciphertext,
                                         crypto_uint8_buf_t iv,
                                         crypto_uint8_buf_t aad,
                                         crypto_uint8_buf_t auth_tag,
                                         crypto_uint8_buf_t *plaintext);

/**
 * Internal GHASH operation of Galois Counter Mode (GCM).
 *
 * GHASH is an operation internal to GCM. It can be used to create
 * custom implementations that do not adhere to the AES-GCM encryption
 * and decryption API provided here. However, custom GCM constructs
 * can be dangerous; for most use cases, prefer the provided
 * encryption and decryption operations.
 *
 * This function initializes the GHASH context and must be called
 * to create a context object.
 *
 * @param hash_subkey Hash subkey (H), 16 bytes
 * @param ctx Output GHASH context object, caller-allocated
 * @return Result of the operation
 */
crypto_status_t otcrypto_gcm_ghash_init(const crypto_blinded_key_t *hash_subkey,
                                        gcm_ghash_context_t *ctx);

/**
 * Internal GHASH operation of Galois Counter Mode (GCM).
 *
 * GHASH is an operation internal to GCM. It can be used to create
 * custom implementations that do not adhere to the AES-GCM encryption
 * and decryption API provided here. However, custom GCM constructs
 * can be dangerous; for most use cases, prefer the provided
 * encryption and decryption operations.
 *
 * This operation adds the input buffer to the message that will
 * be hashed and updates the GHASH context. If the input length is
 * not a multiple of 128 bits, it will be right-padded with zeros.
 * The input length must not be zero.
 *
 * @param ctx GHASH context object
 * @param input Input buffer
 * @return Result of the operation
 */
crypto_status_t otcrypto_gcm_ghash_update(gcm_ghash_context_t *ctx,
                                          crypto_const_uint8_buf_t input);

/**
 * Internal GHASH operation of Galois Counter Mode (GCM).
 *
 * GHASH is an operation internal to GCM. It can be used to create
 * custom implementations that do not adhere to the AES-GCM encryption
 * and decryption API provided here. However, custom GCM constructs
 * can be dangerous; for most use cases, prefer the provided
 * encryption and decryption operations.
 *
 * This operation signals that all input has been provided and
 * extracts the digest from the GHASH context. The digest buffer must
 * be 16 bytes.
 *
 * @param ctx GHASH context object
 * @param digest Output buffer for digest, 16 bytes
 * @return Result of the operation
 */
crypto_status_t otcrypto_gcm_ghash_final(gcm_ghash_context_t *ctx,
                                         crypto_uint8_buf_t digest);

/**
 * Internal AES-GCTR operation of AES Galois Counter Mode (AES-GCM).
 *
 * GCTR is an operation internal to AES-GCM and is based on AES-CTR.
 * It can be used to create custom implementations that do not adhere
 * to the AES-GCM encryption and decryption API provided here.
 * However, custom GCM constructs can be dangerous; for most use
 * cases, prefer the provided encryption and decryption operations.
 *
 * The caller-allocated output buffer must be the same length as the
 * input.
 *
 * @param key AES key for the GCTR operation
 * @param input Input buffer
 * @param output Output buffer (same length as input)
 * @return Result of the operation
 */
crypto_status_t otcrypto_aes_gcm_gctr(const crypto_blinded_key_t *key,
                                      crypto_const_uint8_buf_t input,
                                      crypto_uint8_buf_t output);

/**
 * Performs the AES-KWP authenticated encryption operation.
 *
 * This encrypt function takes an input key `key_to_wrap` and using
 * the encryption key `key_kek` outputs a wrapped key `wrapped_key`.
 *
 * The caller should allocate space for the `wrapped_key` buffer,
 * (same len as `key_to_wrap`), and set the length of expected output
 * in the `len` field of `wrapped_key`. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * @param key_to_wrap Pointer to the blinded key to be wrapped
 * @param key_kek Input Pointer to the blinded encryption key
 * @param wrapped_key Pointer to the output wrapped key
 * @return Result of the aes-kwp encrypt operation
 */
crypto_status_t otcrypto_aes_kwp_encrypt(
    const crypto_blinded_key_t *key_to_wrap,
    const crypto_blinded_key_t *key_kek, crypto_uint8_buf_t *wrapped_key);

/**
 * Performs the AES-KWP authenticated decryption operation.
 *
 * This decrypt function takes a wrapped key `wrapped_key` and using
 * encryption key `key_kek` outputs an unwrapped key `unwrapped_key`.
 *
 * @param wrapped_key Pointer to the input wrapped key
 * @param key_kek Input Pointer to the blinded encryption key
 * @param unwrapped_key Pointer to the output unwrapped key struct
 * @return Result of the aes-kwp decrypt operation
 */
crypto_status_t otcrypto_aes_kwp_decrypt(crypto_const_uint8_buf_t wrapped_key,
                                         const crypto_blinded_key_t *key_kek,
                                         crypto_blinded_key_t *unwrapped_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_
