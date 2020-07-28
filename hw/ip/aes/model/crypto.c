// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/conf.h>
#include <openssl/evp.h>

#include "crypto.h"

/**
 * Get EVP_CIPHER type pointer defined by key_len and mode.
 * If the selected cipher is not supported, the AES-128 ECB type is returned.
 *
 * @param  key_len   Encryption key length in bytes (16, 24, 32)
 * @param  mode      AES cipher mode @see crypto_mode.
 * @return Pointer to EVP_CIPHER type
 */
static const EVP_CIPHER *crypto_get_EVP_cipher(int key_len,
                                               crypto_mode_t mode) {
  const EVP_CIPHER *cipher;

  if (mode == kCryptoAesCbc) {
    if (key_len == 32) {
      cipher = EVP_aes_256_cbc();
    } else if (key_len == 24) {
      cipher = EVP_aes_192_cbc();
    } else {  // key_len = 16
      cipher = EVP_aes_128_cbc();
    }
  } else if (mode == kCryptoAesCfb) {
    if (key_len == 32) {
      cipher = EVP_aes_256_cfb128();
    } else if (key_len == 24) {
      cipher = EVP_aes_192_cfb128();
    } else {  // key_len = 16
      cipher = EVP_aes_128_cfb128();
    }
  } else if (mode == kCryptoAesOfb) {
    if (key_len == 32) {
      cipher = EVP_aes_256_ofb();
    } else if (key_len == 24) {
      cipher = EVP_aes_192_ofb();
    } else {  // key_len = 16
      cipher = EVP_aes_128_ofb();
    }
  } else if (mode == kCryptoAesCtr) {
    if (key_len == 32) {
      cipher = EVP_aes_256_ctr();
    } else if (key_len == 24) {
      cipher = EVP_aes_192_ctr();
    } else {  // key_len = 16
      cipher = EVP_aes_128_ctr();
    }
  } else {  // kCryptoAesEcb
    if (key_len == 32) {
      cipher = EVP_aes_256_ecb();
    } else if (key_len == 24) {
      cipher = EVP_aes_192_ecb();
    } else {  // key_len = 16
      cipher = EVP_aes_128_ecb();
    }
  }

  return cipher;
}

int crypto_encrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, int input_len,
                   const unsigned char *key, int key_len, crypto_mode_t mode) {
  EVP_CIPHER_CTX *ctx;
  int ret;
  int len, output_len;

  // Create new cipher context
  ctx = EVP_CIPHER_CTX_new();
  if (!ctx) {
    printf("ERROR: Creation of cipher context failed\n");
    return -1;
  }

  // Get cipher
  const EVP_CIPHER *cipher = crypto_get_EVP_cipher(key_len, mode);

  // Init encryption context
  ret = EVP_EncryptInit_ex(ctx, cipher, NULL, key, iv);

  if (ret != 1) {
    printf("ERROR: Initialization of encryption context failed\n");
    return -1;
  }

  // Disable padding - It is safe to do so here because we only ever encrypt
  // multiples of 16 bytes (the block size).
  EVP_CIPHER_CTX_set_padding(ctx, 0);

  // Provide encryption input, get first output bytes
  ret = EVP_EncryptUpdate(ctx, output, &output_len, input, input_len);
  if (ret != 1) {
    printf("ERROR: Encryption operation failed\n");
    return -1;
  }

  // Finalize encryption, further bytes might be written
  ret = EVP_EncryptFinal_ex(ctx, output + output_len, &len);
  if (ret != 1) {
    printf("ERROR: Encryption finalizing failed\n");
    return -1;
  }
  output_len += len;

  // Free
  EVP_CIPHER_CTX_free(ctx);

  return output_len;
}

int crypto_decrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, int input_len,
                   const unsigned char *key, int key_len, crypto_mode_t mode) {
  EVP_CIPHER_CTX *ctx;
  int ret;
  int len, output_len;

  // Create new cipher context
  ctx = EVP_CIPHER_CTX_new();
  if (!ctx) {
    printf("ERROR: Creation of cipher context failed\n");
    return -1;
  }

  // Get cipher
  const EVP_CIPHER *cipher = crypto_get_EVP_cipher(key_len, mode);

  // Init decryption context
  ret = EVP_DecryptInit_ex(ctx, cipher, NULL, key, iv);
  if (ret != 1) {
    printf("ERROR: Initialization of decryption context failed\n");
    return -1;
  }

  // Disable padding - It is safe to do so here because we only ever decrypt
  // multiples of 16 bytes (the block size).
  EVP_CIPHER_CTX_set_padding(ctx, 0);

  // Provide decryption input, get first output bytes
  ret = EVP_DecryptUpdate(ctx, output, &output_len, input, input_len);
  if (ret != 1) {
    printf("ERROR: Decryption operation failed\n");
    return -1;
  }

  // Finalize decryption, further bytes might be written
  ret = EVP_DecryptFinal_ex(ctx, output + output_len, &len);
  if (ret != 1) {
    printf("ERROR: Decryption finalizing failed\n");
    return -1;
  }
  output_len += len;

  // Free
  EVP_CIPHER_CTX_free(ctx);

  return output_len;
}
