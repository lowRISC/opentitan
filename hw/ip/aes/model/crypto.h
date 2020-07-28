// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_MODEL_CRYPTO_H_
#define OPENTITAN_HW_IP_AES_MODEL_CRYPTO_H_

/**
 * AES cipher mode
 */
typedef enum crypto_mode {
  kCryptoAesEcb = 1 << 0,
  kCryptoAesCbc = 1 << 1,
  kCryptoAesCfb = 1 << 2,
  kCryptoAesOfb = 1 << 3,
  kCryptoAesCtr = 1 << 4,
  kCryptoAesNone = 1 << 5
} crypto_mode_t;

/**
 * Encrypt using BoringSSL/OpenSSL
 *
 * @param  output    Output cipher text, must be a multiple of 16 bytes
 * @param  iv        16-byte initialization vector
 * @param  input     Input plain text to encode, must be a multiple of 16 bytes
 * @param  input_len Length of the input plain text in bytes, must be a multiple
 *                   of 16
 * @param  key       Encryption key
 * @param  key_len   Encryption key length in bytes (16, 24, 32)
 * @param  mode      AES cipher mode @see crypto_mode.
 * @return Length of the output cipher text in bytes, -1 in case of error
 */
int crypto_encrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, int input_len,
                   const unsigned char *key, int key_len, crypto_mode_t mode);

/**
 * Decrypt using BoringSSL/OpenSSL
 *
 * @param  output    Output plain text, must be a multiple of 16 bytes
 * @param  iv        16-byte initialization vector
 * @param  input     Input cipher text to decode, must be a multiple of 16 bytes
 * @param  input_len Length of the input cipher text in bytes, must be a
 *                   multiple of 16
 * @param  key       Encryption key, decryption key is derived internally
 * @param  key_len   Encryption key length in bytes (16, 24, 32)
 * @param  mode      AES cipher mode @see crypto_mode.
 * @return Length of the output plain text in bytes, -1 in case of error
 */
int crypto_decrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, int input_len,
                   const unsigned char *key, int key_len, crypto_mode_t mode);

#endif  // OPENTITAN_HW_IP_AES_MODEL_CRYPTO_H_
