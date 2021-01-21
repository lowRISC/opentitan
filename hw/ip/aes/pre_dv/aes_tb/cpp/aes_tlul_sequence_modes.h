// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define FORCE_ZERO_MASKS 0
#define FEED_INPUT_WHILE_BUSY 1
#define TEST_STALL 1

#include "aes_modes.h"
#include "aes_tlul_sequence_common.h"
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
  tl_o_exp_resp[i_resp] = {1 << AES_STATUS_IDLE_OFFSET,
                           1 << AES_STATUS_IDLE_OFFSET};
  i_trx++;
  i_resp++;

  // write config
  tl_i_transactions[i_trx] = {
      true,
      0,
      0,
      2,
      0,
      AES_CONFIG,
      0xF,
      FORCE_ZERO_MASKS << AES_CTRL_FORCE_ZERO_MASKS_OFFSET |
          (key_len_bits << AES_CTRL_KEY_LEN_OFFSET) | (mode << 1) |
          (unsigned)op,
      0,
      true};
  i_trx++;

  // confrim config
  tl_i_transactions[i_trx] = {
      true,
      0,
      0,
      2,
      0,
      AES_CONFIG,
      0xF,
      FORCE_ZERO_MASKS << AES_CTRL_FORCE_ZERO_MASKS_OFFSET |
          (key_len_bits << AES_CTRL_KEY_LEN_OFFSET) | (mode << 1) |
          (unsigned)op,
      0,
      true};
  i_trx++;

  // write key share 0
  for (int i = 0; i < key_len / 4; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0,      0, 2,   0, (unsigned)(AES_KEY_SHARE0_0 + 4 * i),
        0xF,  key[i], 0, true};
    i_trx++;
  }
  for (int i = key_len / 4; i < 8; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0,          0, 2,   0, (unsigned)(AES_KEY_SHARE0_0 + 4 * i),
        0xF,  0xFFFFFFFF, 0, true};
    i_trx++;
  }

  // write key share 1
  for (int i = 0; i < key_len / 4; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0, 0, 2,   0, (unsigned)(AES_KEY_SHARE1_0 + 4 * i),
        0xF,  0, 0, true};
    i_trx++;
  }
  for (int i = key_len / 4; i < 8; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0,          0, 2,   0, (unsigned)(AES_KEY_SHARE1_0 + 4 * i),
        0xF,  0xFFFFFFFF, 0, true};
    i_trx++;
  }

  // write iv
  for (int i = 0; i < 4; ++i) {
    tl_i_transactions[i_trx] = {
        true, 0, 0, 2, 0, (unsigned)(AES_IV_0 + 4 * i), 0xF, iv[i], 0, true};
    i_trx++;
  }

  if (FEED_INPUT_WHILE_BUSY) {
    // write input data
    for (int i = 0; i < 4; ++i) {
      tl_i_transactions[i_trx] = {
          true,          0, 0,   2, 0, (unsigned)(AES_DATA_IN_0 + 4 * i), 0xF,
          plain_text[i], 0, true};
      i_trx++;
    }

    // update pointer
    plain_text = plain_text + 4;
  }

  // check input ready
  tl_i_transactions[i_trx] = {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0, 0, true};
  tl_o_exp_resp[i_resp] = {1 << AES_STATUS_INPUT_READY_OFFSET,
                           1 << AES_STATUS_INPUT_READY_OFFSET};
  i_trx++;
  i_resp++;

  for (int j = 0; j < 4; ++j) {
    if (j < 3 || !FEED_INPUT_WHILE_BUSY) {
      // write input data
      for (int i = 0; i < 4; ++i) {
        tl_i_transactions[i_trx] = {
            true,          0, 0,   2, 0, (unsigned)(AES_DATA_IN_0 + 4 * i), 0xF,
            plain_text[i], 0, true};
        i_trx++;
      }

      // update pointer
      plain_text = plain_text + 4;
    }

    // check output valid
    tl_i_transactions[i_trx] = {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0, 0, true};
    tl_o_exp_resp[i_resp] = {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
                             1 << AES_STATUS_OUTPUT_VALID_OFFSET};
    i_trx++;
    i_resp++;

    // wait until the cipher core is stalled
    if (TEST_STALL && j < 3) {
      tl_i_transactions[i_trx] = {true,       4,   0, 2, 0,
                                  AES_STATUS, 0xF, 0, 0, true};
      tl_o_exp_resp[i_resp] = {0x2, 0x2};
      i_trx++;
      i_resp++;
    }

    // read output data
    for (int i = 0; i < 4; ++i) {
      tl_i_transactions[i_trx] = {
          true, 4, 0, 2,   0, (unsigned)(AES_DATA_OUT_0 + 4 * i),
          0xF,  0, 0, true};
      tl_o_exp_resp[i_resp] = {0xFFFFFFFF, cipher_text[i]};
      i_trx++;
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

  int num_groups = 30;

  // Allocate memory
  num_transactions_max =
      (1 + 18 + 4 + 16 + 2 + 20 + 3 * TEST_STALL) * num_groups;
  num_responses_max = (2 + 20 + 3 * TEST_STALL) * num_groups;
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
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvEcb;
      cipher_text = (unsigned *)&kAesModesCipherTextEcb128;
    } else if (i == 1) {
      // ECB - 128 - decode
      op = 1;
      mode = kCryptoAesEcb;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesCipherTextEcb128;
      iv = (unsigned *)&kAesModesIvEcb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 2) {
      // ECB - 192 - encode
      op = 0;
      mode = kCryptoAesEcb;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvEcb;
      cipher_text = (unsigned *)&kAesModesCipherTextEcb192;
    } else if (i == 3) {
      // ECB - 192 - decode
      op = 1;
      mode = kCryptoAesEcb;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesCipherTextEcb192;
      iv = (unsigned *)&kAesModesIvEcb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 4) {
      // ECB - 256 - encode
      op = 0;
      mode = kCryptoAesEcb;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvEcb;
      cipher_text = (unsigned *)&kAesModesCipherTextEcb256;
    } else if (i == 5) {
      // ECB - 256 - decode
      op = 1;
      mode = kCryptoAesEcb;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesCipherTextEcb256;
      iv = (unsigned *)&kAesModesIvEcb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 6) {
      // CBC - 128 - encode
      op = 0;
      mode = kCryptoAesCbc;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCbc;
      cipher_text = (unsigned *)&kAesModesCipherTextCbc128;
    } else if (i == 7) {
      // CBC - 128 - decode
      op = 1;
      mode = kCryptoAesCbc;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesCipherTextCbc128;
      iv = (unsigned *)&kAesModesIvCbc;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 8) {
      // CBC - 192 - encode
      op = 0;
      mode = kCryptoAesCbc;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCbc;
      cipher_text = (unsigned *)&kAesModesCipherTextCbc192;
    } else if (i == 9) {
      // CBC - 192 - decode
      op = 1;
      mode = kCryptoAesCbc;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesCipherTextCbc192;
      iv = (unsigned *)&kAesModesIvCbc;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 10) {
      // CBC - 256 - encode
      op = 0;
      mode = kCryptoAesCbc;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCbc;
      cipher_text = (unsigned *)&kAesModesCipherTextCbc256;
    } else if (i == 11) {
      // CBC - 256 - decode
      op = 1;
      mode = kCryptoAesCbc;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesCipherTextCbc256;
      iv = (unsigned *)&kAesModesIvCbc;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 12) {
      // CFB - 128 - encode
      op = 0;
      mode = kCryptoAesCfb;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCfb;
      cipher_text = (unsigned *)&kAesModesCipherTextCfb128;
    } else if (i == 13) {
      // CFB - 128 - decode
      op = 1;
      mode = kCryptoAesCfb;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesCipherTextCfb128;
      iv = (unsigned *)&kAesModesIvCfb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 14) {
      // CFB - 192 - encode
      op = 0;
      mode = kCryptoAesCfb;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCfb;
      cipher_text = (unsigned *)&kAesModesCipherTextCfb192;
    } else if (i == 15) {
      // CFB - 192 - decode
      op = 1;
      mode = kCryptoAesCfb;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesCipherTextCfb192;
      iv = (unsigned *)&kAesModesIvCfb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 16) {
      // CFB - 256 - encode
      op = 0;
      mode = kCryptoAesCfb;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCfb;
      cipher_text = (unsigned *)&kAesModesCipherTextCfb256;
    } else if (i == 17) {
      // CFB - 256 - decode
      op = 1;
      mode = kCryptoAesCfb;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesCipherTextCfb256;
      iv = (unsigned *)&kAesModesIvCfb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 18) {
      // OFB - 128 - encode
      op = 0;
      mode = kCryptoAesOfb;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvOfb;
      cipher_text = (unsigned *)&kAesModesCipherTextOfb128;
    } else if (i == 19) {
      // OFB - 128 - decode
      op = 1;
      mode = kCryptoAesOfb;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesCipherTextOfb128;
      iv = (unsigned *)&kAesModesIvOfb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 20) {
      // OFB - 192 - encode
      op = 0;
      mode = kCryptoAesOfb;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvOfb;
      cipher_text = (unsigned *)&kAesModesCipherTextOfb192;
    } else if (i == 21) {
      // OFB - 192 - decode
      op = 1;
      mode = kCryptoAesOfb;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesCipherTextOfb192;
      iv = (unsigned *)&kAesModesIvOfb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 22) {
      // OFB - 256 - encode
      op = 0;
      mode = kCryptoAesOfb;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvOfb;
      cipher_text = (unsigned *)&kAesModesCipherTextOfb256;
    } else if (i == 23) {
      // OFB - 256 - decode
      op = 1;
      mode = kCryptoAesOfb;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesCipherTextOfb256;
      iv = (unsigned *)&kAesModesIvOfb;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 24) {
      // CTR - 128 - encode
      op = 0;
      mode = kCryptoAesCtr;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCtr;
      cipher_text = (unsigned *)&kAesModesCipherTextCtr128;
    } else if (i == 25) {
      // CTR - 128 - decode
      op = 1;
      mode = kCryptoAesCtr;
      key_len = 16;
      key = (unsigned *)&kAesModesKey128;
      plain_text = (unsigned *)&kAesModesCipherTextCtr128;
      iv = (unsigned *)&kAesModesIvCtr;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 26) {
      // CTR - 192 - encode
      op = 0;
      mode = kCryptoAesCtr;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCtr;
      cipher_text = (unsigned *)&kAesModesCipherTextCtr192;
    } else if (i == 27) {
      // CTR - 192 - decode
      op = 1;
      mode = kCryptoAesCtr;
      key_len = 24;
      key = (unsigned *)&kAesModesKey192;
      plain_text = (unsigned *)&kAesModesCipherTextCtr192;
      iv = (unsigned *)&kAesModesIvCtr;
      cipher_text = (unsigned *)&kAesModesPlainText;
    } else if (i == 28) {
      // CTR - 256 - encode
      op = 0;
      mode = kCryptoAesCtr;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesPlainText;
      iv = (unsigned *)&kAesModesIvCtr;
      cipher_text = (unsigned *)&kAesModesCipherTextCtr256;
    } else if (i == 29) {
      // CTR - 256 - decode
      op = 1;
      mode = kCryptoAesCtr;
      key_len = 32;
      key = (unsigned *)&kAesModesKey256;
      plain_text = (unsigned *)&kAesModesCipherTextCtr256;
      iv = (unsigned *)&kAesModesIvCtr;
      cipher_text = (unsigned *)&kAesModesPlainText;
    }

    aes_tlul_sequence_modes_gen(&i_transaction, &i_exp_resp, op, mode, key_len,
                                key, iv, plain_text, cipher_text);
  }

  return 0;
}
