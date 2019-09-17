// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef CRYPTO_H_
#define CRYPTO_H_

/**
 * Encrypt using BoringSSL/OpenSSL
 *
 * @param  output    Output cipher text, buffer must be at least 32 bytes
 * @param  iv        16-byte initialization vector
 * @param  input     Input plain text to encode
 * @param  input_len Length of the input plain text in bytes
 * @param  key       Encryption key
 * @param  key_len   Encryption key length in bytes (16, 24, 32)
 * @return Length of the output cipher text in bytes, -1 in case of error
 */
int crypto_encrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, const int input_len,
                   const unsigned char *key, const int key_len);

/**
 * Decrypt using BoringSSL/OpenSSL
 *
 * @param  output    Output plain text, buffer must be at least 32 bytes
 * @param  iv        16-byte initialization vector
 * @param  input     Input cipher text to decode
 * @param  input_len Length of the input cipher text in bytes
 * @param  key       Encryption key, decryption key is derived internally
 * @param  key_len   Encryption key length in bytes (16, 24, 32)
 * @return Length of the output plain text in bytes, -1 in case of error
 */
int crypto_decrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, const int input_len,
                   const unsigned char *key, const int key_len);

#endif  // CRYPTO_H_
