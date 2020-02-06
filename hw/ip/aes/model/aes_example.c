// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aes.h"
#include "aes_example.h"

#include "crypto.h"

#define DEBUG_LEVEL_ENC 0  // 0, 1, 2
#define DEBUG_LEVEL_DEC 0  // 0, 1, 2

#define EXAMPLE 1  // 0, 1

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

int main(int argc, char *argv[]) {
#ifdef USE_BORING_SSL
  char crypto_lib[10] = "BoringSSL";
#else
  char crypto_lib[10] = "OpenSSL";
#endif

  int key_len = 16;
  if (argc > 1) {
    key_len = atoi(argv[1]);
    if (key_len != 16 && key_len != 24 && key_len != 32) {
      printf("WARNING: Unsupported key length %d, switching to 16 (AES-128)\n",
             key_len);
      key_len = 16;
    }
    if (argc > 2) {
      printf(
          "WARNING: Only 1 command line argument supported. Ignoring "
          "further arguments\n");
    }
  }

  int num_rounds = aes_get_num_rounds(key_len);
  if (num_rounds < 0) {
    return num_rounds;
  }

  /*
   * Select plain_text, key and golden ciphertext from example
   */
  const unsigned char *plain_text;
  const unsigned char *key;
  const unsigned char *cipher_text_gold;

  if (EXAMPLE == 0) {
    plain_text = plain_text_0;
    if (key_len == 16) {
      key = key_16_0;
      cipher_text_gold = cipher_text_gold_16_0;
    } else if (key_len == 24) {
      key = key_24_0;
      cipher_text_gold = cipher_text_gold_24_0;
    } else {  // key_len == 32
      key = key_32_0;
      cipher_text_gold = cipher_text_gold_32_0;
    }
  }

  else {  // EXAMPLE == 1
    plain_text = plain_text_1;
    if (key_len == 16) {
      key = key_16_1;
      cipher_text_gold = cipher_text_gold_16_1;
    } else if (key_len == 24) {
      key = key_24_1;
      cipher_text_gold = cipher_text_gold_24_1;
    } else {  // key_len == 32
      key = key_32_1;
      cipher_text_gold = cipher_text_gold_32_1;
    }
  }

  // libcrypto-related variables and buffers
  unsigned char *iv = (unsigned char *)"0000000000000000";
  int cipher_text_len;
  unsigned char cipher_text[16];
  unsigned char decrypted_text[16];

  printf("Encryption key:\t\t");
  aes_print_block((const unsigned char *)key, 16);
  if (key_len > 16) {
    printf("\t\t\t");
    aes_print_block((const unsigned char *)&key[16], key_len - 16);
  }
  printf("Input data:\t\t");
  aes_print_block((const unsigned char *)plain_text, 16);
  printf("\n");

  // intermediate buffers
  unsigned char *full_key =
      (unsigned char *)malloc(key_len * sizeof(unsigned char));
  if (full_key == NULL) {
    printf("ERROR: malloc() failed\n");
    return -ENOMEM;
  }
  unsigned char state[16];
  unsigned char state_lib[16];
  unsigned char round_key[16];
  unsigned char inv_round_key[16];
  unsigned char rcon;

  //
  // ENCRYPTION
  //

  // init
  // copy plain text to state
  for (int i = 0; i < 16; i++) {
    state[i] = plain_text[i];
  }
  // copy first 16 bytes of key to round key
  for (int i = 0; i < 16; i++) {
    round_key[i] = key[i];
  }
  // copy key to long key
  for (int i = 0; i < key_len; i++) {
    full_key[i] = key[i];
  }
  // reset rcon
  rcon = 0x00;

  if (DEBUG_LEVEL_ENC > 0) {
    printf("Init input:\t\t");
    aes_print_block((const unsigned char *)state, 16);
    printf("Init key:\t\t");
    aes_print_block((const unsigned char *)round_key, 16);
  }

  // add round key
  aes_add_round_key(state, round_key);

  // rounds
  for (int j = 0; j < num_rounds; j++) {
    if (DEBUG_LEVEL_ENC > 0) {
      printf("Round %i input:\t\t", j);
      aes_print_block((const unsigned char *)state, 16);
    }

    // sub bytes
    aes_sub_bytes(state);
    if (DEBUG_LEVEL_ENC > 1) {
      printf("Round %i SubBytes:\t", j);
      aes_print_block((const unsigned char *)state, 16);
    }

    // shift rows
    aes_shift_rows(state);
    if (DEBUG_LEVEL_ENC > 1) {
      printf("Round %i ShiftRows:\t", j);
      aes_print_block((const unsigned char *)state, 16);
    }

    // mix columns
    if (j < (num_rounds - 1)) {
      aes_mix_columns(state);
      if (DEBUG_LEVEL_ENC > 1) {
        printf("Round %i MixColumns:\t", j);
        aes_print_block((const unsigned char *)state, 16);
      }
    }

    // expand key
    aes_key_expand(round_key, full_key, key_len, &rcon, j);
    if (DEBUG_LEVEL_ENC > 0) {
      printf("Round %i key:\t\t", j);
      aes_print_block((const unsigned char *)round_key, 16);
    }

    // add round key
    aes_add_round_key(state, round_key);
  }

  // print
  printf("Encryption output:\t");
  aes_print_block((const unsigned char *)state, 16);
  printf("\n");

  // check state vs AES model/lib
  aes_encrypt_block(plain_text, key, key_len, state_lib);
  if (check_block(state, state_lib, 0)) {
    printf("ERROR: state does not match AES model output\n");
  }

  // check state versus gold
  if (!check_block(state, cipher_text_gold, 1)) {
    printf("SUCCESS: state matches golden cipher text\n");
  } else {
    printf("ERROR: state does not match golden cipher text\n");
  }

  // check state vs BoringSSL/OpenSSL
  cipher_text_len = crypto_encrypt(cipher_text, iv, plain_text, 16, key,
                                   key_len, kCryptoAesEcb);
  if (!check_block(state, cipher_text, 0)) {
    printf("SUCCESS: state matches %s cipher text\n", crypto_lib);
  } else {
    printf("ERROR: state does not match %s cipher text\n", crypto_lib);
    return 0;
  }
  printf("\n");

  //
  // DECRYPTION using Equivalent Inverse Cipher
  //

  //
  // generate decryption key
  //
  // copy first 16 bytes of key to round key
  for (int i = 0; i < 16; i++) {
    round_key[i] = key[i];
  }
  // copy key to long key
  for (int i = 0; i < key_len; i++) {
    full_key[i] = key[i];
  }
  // reset rcon
  rcon = 0x00;

  for (int j = 0; j < num_rounds; j++) {
    aes_key_expand(round_key, full_key, key_len, &rcon, j);
  }

  // init
  // cyper text is already in state
  // round key is prepared already
  // reset rcon
  rcon = 0x00;

  if (DEBUG_LEVEL_DEC > 0) {
    printf("Init input:\t\t");
    aes_print_block((const unsigned char *)state, 16);
    printf("Init key:\t\t");
    aes_print_block((const unsigned char *)round_key, 16);
  }

  // add round key
  aes_add_round_key(state, round_key);

  // rounds
  for (int j = 0; j < num_rounds; j++) {
    if (DEBUG_LEVEL_DEC > 0) {
      printf("Round %i input:\t\t", j);
      aes_print_block((const unsigned char *)state, 16);
    }

    // sub bytes
    aes_inv_sub_bytes(state);
    if (DEBUG_LEVEL_DEC > 1) {
      printf("Round %i InvSubBytes:\t", j);
      aes_print_block((const unsigned char *)state, 16);
    }

    // shift rows
    aes_inv_shift_rows(state);
    if (DEBUG_LEVEL_DEC > 1) {
      printf("Round %i InvShiftRows:\t", j);
      aes_print_block((const unsigned char *)state, 16);
    }

    // mix columns
    if (j < (num_rounds - 1)) {
      aes_inv_mix_columns(state);
      if (DEBUG_LEVEL_DEC > 1) {
        printf("Round %i InvMixColumns:\t", j);
        aes_print_block((const unsigned char *)state, 16);
      }
    }

    // expand key
    aes_inv_key_expand(round_key, full_key, key_len, &rcon, j);
    if (DEBUG_LEVEL_DEC > 0) {
      printf("Round %i key:\t\t", j);
      aes_print_block((const unsigned char *)round_key, 16);
    }

    // mix columns on round key
    for (int i = 0; i < 16; i++) {
      inv_round_key[i] = round_key[i];
    }
    if (j < (num_rounds - 1)) {
      aes_inv_mix_columns(inv_round_key);
      if (DEBUG_LEVEL_DEC > 0) {
        printf("Round %i mixed key:\t", j);
        aes_print_block((const unsigned char *)inv_round_key, 16);
      }
    }

    // add round key
    aes_add_round_key(state, inv_round_key);
  }

  // print
  printf("Decryption Output:\t");
  aes_print_block((const unsigned char *)state, 16);
  printf("\n");

  // check state vs AES model/lib
  aes_decrypt_block(cipher_text, key, key_len, state_lib);
  if (check_block(state, state_lib, 0)) {
    printf("ERROR: state does not match AES model output\n");
  }

  // check state versus gold/plain_text
  if (!check_block(state, plain_text, 1)) {
    printf("SUCCESS: state matches expected plain text\n");
  } else {
    printf("ERROR: state does not match expected plain text\n");
  }

  // check state vs BoringSSL/OpenSSL
  crypto_decrypt(decrypted_text, iv, cipher_text, cipher_text_len, key, key_len,
                 kCryptoAesEcb);
  if (!check_block(state, decrypted_text, 0)) {
    printf("SUCCESS: state matches %s decrypted text\n", crypto_lib);
  } else {
    printf("ERROR: state does not match %s decrypted text\n", crypto_lib);
    return 0;
  }

  return 0;
}
