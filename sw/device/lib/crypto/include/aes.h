// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_

#include "datatypes.h"

/**
 * @file
 * @brief AES operations for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define AES mode of operation.
 *
 * Values are hardened.
 */
typedef enum otcrypto_aes_mode {
  // AES ECB mode (electronic codebook mode).
  kOtcryptoAesModeEcb = 0x533,
  // AES CBC mode (cipher block chaining mode).
  kOtcryptoAesModeCbc = 0x45d,
  // AES CFB mode (cipher feedback mode).
  kOtcryptoAesModeCfb = 0xcd2,
  // AES OFB mode (output feedback mode).
  kOtcryptoAesModeOfb = 0x39a,
  // AES CTR mode (counter mode).
  kOtcryptoAesModeCtr = 0xd2c,
} otcrypto_aes_mode_t;

/**
 * Enum to define AES operation to be performed.
 *
 * Values are hardened.
 */
typedef enum otcrypto_aes_operation {
  // AES operation mode encrypt.
  kOtcryptoAesOperationEncrypt = 0x2b6,
  // AES operation mode decrypt.
  kOtcryptoAesOperationDecrypt = 0x5f0,
} otcrypto_aes_operation_t;

/**
 * Enum to define padding scheme for AES data.
 *
 * Values are hardened.
 */
typedef enum otcrypto_aes_padding {
  // Pads with value same as the number of padding bytes.
  kOtcryptoAesPaddingPkcs7 = 0xe7f,
  // Pads with 0x80 (10000000), followed by zero bytes.
  kOtcryptoAesPaddingIso9797M2 = 0xfac,
  // Add no padding.
  kOtcryptoAesPaddingNull = 0x8ce,
} otcrypto_aes_padding_t;

/**
 * Get the number of blocks needed for the plaintext length and padding mode.
 *
 * This returns the size of the padded plaintext, which is the same as the
 * ciphertext size. Returns `kOtcryptoStatusValueBadArgs` if the padding mode
 * and length are incompatible (for instance, if the padding mode is "no
 * padding" but the input length is not a multiple of the AES block size).
 *
 * @param plaintext_len Plaintext data length in bytes.
 * @param aes_padding Padding scheme to be used for the data.
 * @return Size of the padded input or ciphertext.
 * @return Result of the operation.
 */
otcrypto_status_t otcrypto_aes_padded_plaintext_length(
    size_t plaintext_len, otcrypto_aes_padding_t aes_padding,
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
otcrypto_status_t otcrypto_aes(otcrypto_blinded_key_t *key,
                               otcrypto_word32_buf_t iv,
                               otcrypto_aes_mode_t aes_mode,
                               otcrypto_aes_operation_t aes_operation,
                               otcrypto_const_byte_buf_t cipher_input,
                               otcrypto_aes_padding_t aes_padding,
                               otcrypto_byte_buf_t cipher_output);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_AES_H_
