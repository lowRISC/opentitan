// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aes.h"
#include "aes_modes.h"

#include "crypto.h"

#ifdef USE_BORING_SSL
char crypto_lib[10] = "BoringSSL";
#else
char crypto_lib[10] = "OpenSSL";
#endif

static int check_block(const unsigned char *actual,
                       const unsigned char *expected, const int print) {
  for (int i = 0; i < 16; i++) {
    if (actual[i] != expected[i]) {
      if (print) {
        printf("ERROR: block mismatch. Found %#x, expected %#x\n", actual[i],
               expected[i]);
      }
      return 1;
    }
  }

  return 0;
}

static int crypto_compare(const unsigned char *cipher_text,
                          const unsigned char *iv,
                          const unsigned char *plain_text, int len,
                          const unsigned char *key, int key_len,
                          crypto_mode_t mode) {
  const unsigned char *data_in;
  int ret_len;
  int ret_len_exp = len;

  // Enc
  unsigned char *data_out =
      (unsigned char *)malloc(ret_len_exp * sizeof(unsigned char));
  if (data_out == NULL) {
    printf("ERROR: malloc() failed\n");
    return 1;
  }
  data_in = plain_text;

  ret_len = crypto_encrypt(data_out, iv, data_in, len, key, key_len, mode);
  if (ret_len != ret_len_exp) {
    printf("ERROR: ret_len = %i, expected %i. Aborting now\n", ret_len,
           ret_len_exp);
    return 1;
  }

  for (int j = 0; j < len / 16; ++j) {
    if (!check_block(&data_out[j * 16], &cipher_text[j * 16], 1)) {
      printf("SUCCESS: %s encrypt output matches NIST example cipher text\n",
             crypto_lib);
    } else {
      printf(
          "ERROR: %s encrypt output does not match NIST example cipher text\n",
          crypto_lib);
      printf("Input: \t\t");
      aes_print_block(&data_in[j * 16], 16);
      printf("Output: \t");
      aes_print_block(&data_out[j * 16], 16);
      printf("Expected: \t");
      aes_print_block(&cipher_text[j * 16], 16);
      return 1;
    }
  }

  // Dec
  unsigned char *data_in_dec =
      (unsigned char *)malloc(ret_len_exp * sizeof(unsigned char));
  if (data_in_dec == NULL) {
    printf("ERROR: malloc() failed\n");
    return 1;
  }
  for (int j = 0; j < ret_len; ++j) {
    data_in_dec[j] = data_out[j];
  }

  ret_len =
      crypto_decrypt(data_out, iv, data_in_dec, ret_len, key, key_len, mode);
  if (ret_len != len) {
    printf("ERROR: ret_len = %i, expected %i. Aborting now\n", ret_len, len);
    return 1;
  }

  for (int j = 0; j < len / 16; ++j) {
    if (!check_block(&data_out[j * 16], &plain_text[j * 16], 1)) {
      printf("SUCCESS: %s decrypt output matches NIST example plain text\n",
             crypto_lib);
    } else {
      printf(
          "ERROR: %s decrypt output does not match NIST example plain text\n",
          crypto_lib);
      printf("Input: \t\t");
      aes_print_block(&data_in_dec[j * 16], 16);
      printf("Output: \t");
      aes_print_block(&data_out[j * 16], 16);
      printf("Expected: \t");
      aes_print_block(&plain_text[j * 16], 16);
      return 1;
    }
  }

  free(data_out);
  free(data_in_dec);

  return 0;
}

int main(int argc, char *argv[]) {
  const int len = 64;
  int key_len;
  crypto_mode_t mode;
  const unsigned char *iv;
  const unsigned char *key;
  const unsigned char *cipher_text;

  /////////
  // ECB //
  /////////
  iv = aes_modes_iv_ecb;
  mode = kCryptoAesEcb;

  for (int i = 0; i < 3; ++i) {
    if (i == 0) {
      printf("ECB AES-128\n");
      key_len = 16;
      key = aes_modes_key_128;
      cipher_text = aes_modes_cipher_text_ecb_128;
    } else if (i == 1) {
      printf("ECB AES-192\n");
      key_len = 24;
      key = aes_modes_key_192;
      cipher_text = aes_modes_cipher_text_ecb_192;
    } else {  // i==2
      printf("ECB AES-256\n");
      key_len = 32;
      key = aes_modes_key_256;
      cipher_text = aes_modes_cipher_text_ecb_256;
    }

    if (crypto_compare(cipher_text, iv, aes_modes_plain_text, len, key, key_len,
                       mode)) {
      return 1;
    }
  }

  /////////
  // CBC //
  /////////
  iv = aes_modes_iv_cbc;
  mode = kCryptoAesCbc;

  for (int i = 0; i < 3; ++i) {
    if (i == 0) {
      printf("CBC AES-128\n");
      key_len = 16;
      key = aes_modes_key_128;
      cipher_text = aes_modes_cipher_text_cbc_128;
    } else if (i == 1) {
      printf("CBC AES-192\n");
      key_len = 24;
      key = aes_modes_key_192;
      cipher_text = aes_modes_cipher_text_cbc_192;
    } else {  // i==2
      printf("CBC AES-256\n");
      key_len = 32;
      key = aes_modes_key_256;
      cipher_text = aes_modes_cipher_text_cbc_256;
    }

    if (crypto_compare(cipher_text, iv, aes_modes_plain_text, len, key, key_len,
                       mode)) {
      return 1;
    }
  }

  /////////
  // CTR //
  /////////
  iv = aes_modes_iv_ctr;
  mode = kCryptoAesCtr;

  for (int i = 0; i < 3; ++i) {
    if (i == 0) {
      printf("CTR AES-128\n");
      key_len = 16;
      key = aes_modes_key_128;
      cipher_text = aes_modes_cipher_text_ctr_128;
    } else if (i == 1) {
      printf("CTR AES-192\n");
      key_len = 24;
      key = aes_modes_key_192;
      cipher_text = aes_modes_cipher_text_ctr_192;
    } else {  // i==2
      printf("CTR AES-256\n");
      key_len = 32;
      key = aes_modes_key_256;
      cipher_text = aes_modes_cipher_text_ctr_256;
    }

    if (crypto_compare(cipher_text, iv, aes_modes_plain_text, len, key, key_len,
                       mode)) {
      return 1;
    }
  }

  return 0;
}
