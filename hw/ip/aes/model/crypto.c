// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <openssl/conf.h>
#include <openssl/evp.h>

int crypto_encrypt(unsigned char *output, const unsigned char *iv,
                   const unsigned char *input, const int input_len,
                   const unsigned char *key, const int key_len) {
  EVP_CIPHER_CTX *ctx;
  int ret;
  int len, output_len;

  // Create new cipher context
  ctx = EVP_CIPHER_CTX_new();
  if (!ctx) {
    printf("ERROR: Creation of cipher context failed\n");
    return -1;
  }

  // Init encryption context
  if (key_len == 16) {
    ret = EVP_EncryptInit_ex(ctx, EVP_aes_128_ecb(), NULL, key, iv);
  } else if (key_len == 24) {
    ret = EVP_EncryptInit_ex(ctx, EVP_aes_192_ecb(), NULL, key, iv);
  } else {  // key_len = 32
    ret = EVP_EncryptInit_ex(ctx, EVP_aes_256_ecb(), NULL, key, iv);
  }
  if (ret != 1) {
    printf("ERROR: Initialization of encryption context failed\n");
    return -1;
  }

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
                   const unsigned char *input, const int input_len,
                   const unsigned char *key, const int key_len) {
  EVP_CIPHER_CTX *ctx;
  int ret;
  int len, output_len;

  // Create new cipher context
  ctx = EVP_CIPHER_CTX_new();
  if (!ctx) {
    printf("ERROR: Creation of cipher context failed\n");
    return -1;
  }

  // Init decryption context
  if (key_len == 16) {
    ret = EVP_DecryptInit_ex(ctx, EVP_aes_128_ecb(), NULL, key, iv);
  } else if (key_len == 24) {
    ret = EVP_DecryptInit_ex(ctx, EVP_aes_192_ecb(), NULL, key, iv);
  } else {  // key_len == 32
    ret = EVP_DecryptInit_ex(ctx, EVP_aes_256_ecb(), NULL, key, iv);
  }
  if (ret != 1) {
    printf("ERROR: Initialization of decryption context failed\n");
    return -1;
  }

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
