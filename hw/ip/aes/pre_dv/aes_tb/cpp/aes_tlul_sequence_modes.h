// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define FEED_INPUT_WHILE_BUSY 1

#define AES_KEY0 0x0
#define AES_IV0 0x20
#define AES_DATA_IN0 0x20
#define AES_DATA_OUT0 0x30
#define AES_CONFIG 0x40
#define AES_STATUS 0x48

#include "aes_modes.h"
#include "crypto.h"

TLI *tl_i_transactions;
int num_transactions_max;
EXP_RESP *tl_o_exp_resp;
int num_responses_max;

static void aes_tlul_sequence_modes_gen(int *i_transaction, int *i_exp_resp,
                                        int op, crypto_mode_t mode, int key_len,
                                        unsigned *key, unsigned *iv,
                                        unsigned *plain_text,
                                        unsigned *cipher_text) {
  int i_trx = *i_transaction;
  int i_resp = *i_exp_resp;

  unsigned key_len_bits;

  // key_len_bits is one-hot
  if (key_len == 32) {
    key_len_bits = 0x4;
  } else if (key_len == 24) {
    key_len_bits = 0x2;
  } else {
    key_len_bits = 0x1;
  }

  // check status idle
  tl_i_transactions[i_trx] = {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0, 0, true};
  tl_o_exp_resp[i_resp] = {0x1, 0x1};
  i_trx++;
  i_resp++;

  // write config
  tl_i_transactions[i_trx] = {
      true, 0,   0, 2, 0, AES_CONFIG, 0xF, (key_len_bits << 1) | (unsigned)op,
      0,    true};
  i_trx++;

  // write key
  for (int i = 0; i < key_len / 4; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0, 0, 2, 0, (unsigned)(AES_KEY0 + 4 * i), 0xF, key[i], 0, true};
    i_trx++;
  }
  for (int i = key_len / 4; i < 8; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0,          0, 2,   0, (unsigned)(AES_KEY0 + 4 * i),
        0xF,  0xFFFFFFFF, 0, true};
    i_trx++;
  }

  // write iv
  // for (int i=0; i<4; ++i) {
  //  tl_i_transactions[i_trx] =
  //    {true, 0, 0, 2, 0, AES_IV0 + 4*i, 0xF, iv[i], 0, true};
  //  i_trx++;
  //}

  if (FEED_INPUT_WHILE_BUSY) {
    // write input data
    for (int i = 0; i < 4; ++i) {
      tl_i_transactions[i_trx] = {
          true,          0, 0,   2, 0, (unsigned)(AES_DATA_IN0 + 4 * i), 0xF,
          plain_text[i], 0, true};
      i_trx++;
    }

    // update pointer
    plain_text = plain_text + 4;
  }

  // check input ready
  tl_i_transactions[i_trx] = {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0, 0, true};
  tl_o_exp_resp[i_resp] = {0x8, 0x8};
  i_trx++;
  i_resp++;

  for (int j = 0; j < 4; ++j) {
    if (j < 3 || !FEED_INPUT_WHILE_BUSY) {
      // write input data
      for (int i = 0; i < 4; ++i) {
        tl_i_transactions[i_trx] = {
            true,          0, 0,   2, 0, (unsigned)(AES_DATA_IN0 + 4 * i), 0xF,
            plain_text[i], 0, true};
        i_trx++;
      }

      // update pointer
      plain_text = plain_text + 4;
    }

    // check output valid
    tl_i_transactions[i_trx] = {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0, 0, true};
    tl_o_exp_resp[i_resp] = {0x4, 0x4};
    i_trx++;
    i_resp++;

    // read output data
    for (int i = 0; i < 4; ++i) {
      tl_i_transactions[i_trx] = {
          true, 4, 0, 2, 0, (unsigned)(AES_DATA_OUT0 + 4 * i), 0xF, 0, 0, true};
      tl_o_exp_resp[i_resp] = {0xFFFFFFFF, cipher_text[i]}, i_trx++;
      i_resp++;
    }

    // update pointer
    cipher_text = cipher_text + 4;
  }

  *i_transaction = i_trx;
  *i_exp_resp = i_resp;
}

int aes_tlul_sequence_modes_gen_all() {
  int op;
  crypto_mode_t mode;
  int key_len;
  unsigned *key;
  unsigned *iv;
  unsigned *plain_text;
  unsigned *cipher_text;

  int num_groups = 6;

  // Allocate memory
  num_transactions_max = (1 + 9 + 16 + 2 + 20) * num_groups;
  num_responses_max = (2 + 20) * num_groups;
  tl_i_transactions = (TLI *)malloc(num_transactions_max * sizeof(TLI));
  if (tl_i_transactions == NULL) {
    printf("ERROR: malloc() failed\n");
    return -1;
  }
  tl_o_exp_resp = (EXP_RESP *)malloc(num_responses_max * sizeof(EXP_RESP));
  if (tl_o_exp_resp == NULL) {
    printf("ERROR: malloc() failed\n");
    return -1;
  }
  int i_transaction = 0;
  int i_exp_resp = 0;

  for (int i = 0; i < num_groups; ++i) {
    if (i == 0) {
      // ECB - 128 - encode
      op = 0;
      mode = kCryptoAesEcb;
      key_len = 16;
      key = (unsigned *)&aes_modes_key_128;
      plain_text = (unsigned *)&aes_modes_plain_text;
      iv = (unsigned *)&aes_modes_iv_ecb;
      cipher_text = (unsigned *)&aes_modes_cipher_text_ecb_128;
    } else if (i == 1) {
      // ECB - 128 - decode
      op = 1;
      mode = kCryptoAesEcb;
      key_len = 16;
      key = (unsigned *)&aes_modes_key_128;
      plain_text = (unsigned *)&aes_modes_cipher_text_ecb_128;
      iv = (unsigned *)&aes_modes_iv_ecb;
      cipher_text = (unsigned *)&aes_modes_plain_text;
    } else if (i == 2) {
      // ECB - 192 - encode
      op = 0;
      mode = kCryptoAesEcb;
      key_len = 24;
      key = (unsigned *)&aes_modes_key_192;
      plain_text = (unsigned *)&aes_modes_plain_text;
      iv = (unsigned *)&aes_modes_iv_ecb;
      cipher_text = (unsigned *)&aes_modes_cipher_text_ecb_192;
    } else if (i == 3) {
      // ECB - 192 - decode
      op = 1;
      mode = kCryptoAesEcb;
      key_len = 24;
      key = (unsigned *)&aes_modes_key_192;
      plain_text = (unsigned *)&aes_modes_cipher_text_ecb_192;
      iv = (unsigned *)&aes_modes_iv_ecb;
      cipher_text = (unsigned *)&aes_modes_plain_text;
    } else if (i == 4) {
      // ECB - 256 - encode
      op = 0;
      mode = kCryptoAesEcb;
      key_len = 32;
      key = (unsigned *)&aes_modes_key_256;
      plain_text = (unsigned *)&aes_modes_plain_text;
      iv = (unsigned *)&aes_modes_iv_ecb;
      cipher_text = (unsigned *)&aes_modes_cipher_text_ecb_256;
    } else if (i == 5) {
      // ECB - 256 - decode
      op = 1;
      mode = kCryptoAesEcb;
      key_len = 32;
      key = (unsigned *)&aes_modes_key_256;
      plain_text = (unsigned *)&aes_modes_cipher_text_ecb_256;
      iv = (unsigned *)&aes_modes_iv_ecb;
      cipher_text = (unsigned *)&aes_modes_plain_text;
    }
    aes_tlul_sequence_modes_gen(&i_transaction, &i_exp_resp, op, mode, key_len,
                                key, iv, plain_text, cipher_text);
  }

  return 0;
}
