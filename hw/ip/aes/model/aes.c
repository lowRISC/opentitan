// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "aes.h"

int aes_encrypt_block(const unsigned char *plain_text, const unsigned char *key,
                      const int key_len, unsigned char *cipher_text) {
  int num_rounds = aes_get_num_rounds(key_len);
  if (num_rounds < 0) {
    printf("ERROR: aes_get_num_rounds() failed\n");
    return -EINVAL;
  }

  unsigned char rcon;
  unsigned char state[16];
  unsigned char round_key[16];
  unsigned char *full_key =
      (unsigned char *)malloc(key_len * sizeof(unsigned char));
  if (full_key == NULL) {
    printf("ERROR: malloc() failed\n");
    return -ENOMEM;
  }

  // init
  for (int i = 0; i < 16; i++) {
    state[i] = plain_text[i];
  }
  for (int i = 0; i < key_len; i++) {
    full_key[i] = key[i];
  }
  for (int i = 0; i < 16; i++) {
    round_key[i] = full_key[i];
  }
  rcon = 0;

  // ecnrypt
  aes_add_round_key(state, round_key);
  for (int j = 0; j < num_rounds; j++) {
    aes_sub_bytes(state);
    aes_shift_rows(state);
    if (j < (num_rounds - 1)) {
      aes_mix_columns(state);
    }
    aes_key_expand(round_key, full_key, key_len, &rcon, j);
    aes_add_round_key(state, round_key);
  }

  // finish
  for (int i = 0; i < 16; i++) {
    cipher_text[i] = state[i];
  }

  free(full_key);

  return 0;
}

int aes_decrypt_block(const unsigned char *cipher_text,
                      const unsigned char *key, const int key_len,
                      unsigned char *plain_text) {
  int num_rounds = aes_get_num_rounds(key_len);
  if (num_rounds < 0) {
    printf("ERROR: aes_get_num_rounds() failed\n");
    return -EINVAL;
  }

  unsigned char rcon;
  unsigned char state[16];
  unsigned char round_key[16];
  unsigned char *full_key =
      (unsigned char *)malloc(key_len * sizeof(unsigned char));
  if (full_key == NULL) {
    printf("ERROR: malloc() failed\n");
    return -ENOMEM;
  }

  // init
  for (int i = 0; i < 16; i++) {
    state[i] = cipher_text[i];
  }
  for (int i = 0; i < key_len; i++) {
    full_key[i] = key[i];
  }
  for (int i = 0; i < 16; i++) {
    round_key[i] = full_key[i];
  }
  rcon = 0;

  // get decryption start key
  for (int j = 0; j < num_rounds; j++) {
    aes_key_expand(round_key, full_key, key_len, &rcon, j);
  }
  rcon = 0;

  // decrypt - using Equivalent Inverse Cipher
  aes_add_round_key(state, round_key);
  for (int j = 0; j < num_rounds; j++) {
    aes_inv_sub_bytes(state);
    aes_inv_shift_rows(state);
    if (j < (num_rounds - 1)) {
      aes_inv_mix_columns(state);
    }
    aes_inv_key_expand(round_key, full_key, key_len, &rcon, j);
    if (j < (num_rounds - 1)) {
      aes_inv_mix_columns(round_key);
    }
    aes_add_round_key(state, round_key);
  }

  // finish
  for (int i = 0; i < 16; i++) {
    plain_text[i] = state[i];
  }

  free(full_key);
  return 0;
}

void aes_print_block(const unsigned char *data, const int num_bytes) {
  for (int i = 0; i < num_bytes; i++) {
    if ((i > 0) && (i % 8 == 0)) {
      printf("- ");
    }
    printf("%x%x ", data[i] >> 4, data[i] & 0xF);
  }
  printf("\n");

  return;
}

int aes_get_num_rounds(int key_len) {
  int num_rounds = 0;
  int num_k = key_len / 4;

  if (num_k == 4) {
    num_rounds = 10;
  } else if (num_k == 6) {
    num_rounds = 12;
  } else if (num_k == 8) {
    num_rounds = 14;
  } else {
    printf("ERROR: key_len = %i not supported\n", key_len);
    return -EINVAL;
  }

  return num_rounds;
}

static unsigned char aes_mul2(unsigned char in) {
  // set individual bits of out
  unsigned char out = 0x0;

  //        extract bits     possible xor    shift to right position
  out |= (((in >> 7) & 0x1)) << 0;
  out |= (((in >> 0) & 0x1) ^ ((in >> 7) & 0x1)) << 1;
  out |= (((in >> 1) & 0x1)) << 2;
  out |= (((in >> 2) & 0x1) ^ ((in >> 7) & 0x1)) << 3;
  out |= (((in >> 3) & 0x1) ^ ((in >> 7) & 0x1)) << 4;
  out |= (((in >> 4) & 0x1)) << 5;
  out |= (((in >> 5) & 0x1)) << 6;
  out |= (((in >> 6) & 0x1)) << 7;

  return out;
}

static unsigned char aes_mul4(unsigned char in) {
  // return aes_mul2(aes_mul2(in));

  // set individual bits of out
  unsigned char out = 0x0;

  //        extract bits     possible xor    shift to right position
  out |= (((in >> 6) & 0x1)) << 0;
  out |= (((in >> 7) & 0x1) ^ ((in >> 6) & 0x1)) << 1;
  out |= (((in >> 0) & 0x1) ^ ((in >> 7) & 0x1)) << 2;
  out |= (((in >> 1) & 0x1) ^ ((in >> 6) & 0x1)) << 3;
  out |= (((in >> 2) & 0x1) ^ ((in >> 7) & 0x1) ^ ((in >> 6) & 0x1)) << 4;
  out |= (((in >> 3) & 0x1) ^ ((in >> 7) & 0x1)) << 5;
  out |= (((in >> 4) & 0x1)) << 6;
  out |= (((in >> 5) & 0x1)) << 7;

  return out;
}

void aes_add_round_key(unsigned char *state, const unsigned char *round_key) {
  for (int i = 0; i < 16; i++) {
    state[i] ^= round_key[i];
  }

  return;
}

void aes_sub_bytes(unsigned char *state) {
  // substitute
  for (int i = 0; i < 16; i++) {
    state[i] = sbox[state[i]];
  }

  return;
}

void aes_inv_sub_bytes(unsigned char *state) {
  // substitute
  for (int i = 0; i < 16; i++) {
    state[i] = inv_sbox[state[i]];
  }

  return;
}

void aes_shift_rows(unsigned char *state) {
  unsigned char temp[16];

  // copy state to temp
  for (int i = 0; i < 16; i++) {
    temp[i] = state[i];
  }

  // extract state from temp
  // Row 1
  state[1] = temp[5];
  state[5] = temp[9];
  state[9] = temp[13];
  state[13] = temp[1];

  // Row 2
  state[2] = temp[10];
  state[6] = temp[14];
  state[10] = temp[2];
  state[14] = temp[6];

  // Row 3
  state[3] = temp[15];
  state[7] = temp[3];
  state[11] = temp[7];
  state[15] = temp[11];

  return;
}

void aes_inv_shift_rows(unsigned char *state) {
  unsigned char temp[16];

  // copy state to temp
  for (int i = 0; i < 16; i++) {
    temp[i] = state[i];
  }

  // extract state from temp
  // Row 1
  state[1] = temp[13];
  state[5] = temp[1];
  state[9] = temp[5];
  state[13] = temp[9];

  // Row 2 -> same as for encryption
  state[2] = temp[10];
  state[6] = temp[14];
  state[10] = temp[2];
  state[14] = temp[6];

  // Row 3
  state[3] = temp[7];
  state[7] = temp[11];
  state[11] = temp[15];
  state[15] = temp[3];

  return;
}

void aes_mix_columns(unsigned char *state) {
  unsigned char temp[16];

  // copy state to temp
  for (int i = 0; i < 16; i++) {
    temp[i] = state[i];
  }

  // do the matrix mul column by column
  unsigned char x3, x2, x1, x0;
  for (int j = 0; j < 4; j++) {
    // see satoh_compact_2001.pdf

    x3 = temp[0 + j * 4] ^ temp[1 + j * 4];
    x2 = temp[1 + j * 4] ^ temp[2 + j * 4];
    x1 = temp[2 + j * 4] ^ temp[3 + j * 4];
    x0 = temp[3 + j * 4] ^ temp[0 + j * 4];

    state[0 + j * 4] = aes_mul2(x3) ^ x1 ^ temp[1 + j * 4];
    state[1 + j * 4] = aes_mul2(x2) ^ x1 ^ temp[0 + j * 4];
    state[2 + j * 4] = aes_mul2(x1) ^ x3 ^ temp[3 + j * 4];
    state[3 + j * 4] = aes_mul2(x0) ^ x3 ^ temp[2 + j * 4];
  }

  return;
}

void aes_inv_mix_columns(unsigned char *state) {
  unsigned char temp[16];

  // copy state to temp
  for (int i = 0; i < 16; i++) {
    temp[i] = state[i];
  }

  // do the matrix mul column by column
  unsigned char x3, x2, x1, x0;
  unsigned char y2, y1, y0, z1, z0;
  for (int j = 0; j < 4; j++) {
    // see satoh_compact_2001.pdf

    // first step equal to encryption
    x3 = temp[0 + j * 4] ^ temp[1 + j * 4];
    x2 = temp[1 + j * 4] ^ temp[2 + j * 4];
    x1 = temp[2 + j * 4] ^ temp[3 + j * 4];
    x0 = temp[3 + j * 4] ^ temp[0 + j * 4];

    state[0 + j * 4] = aes_mul2(x3) ^ x1 ^ temp[1 + j * 4];
    state[1 + j * 4] = aes_mul2(x2) ^ x1 ^ temp[0 + j * 4];
    state[2 + j * 4] = aes_mul2(x1) ^ x3 ^ temp[3 + j * 4];
    state[3 + j * 4] = aes_mul2(x0) ^ x3 ^ temp[2 + j * 4];

    // second & third step
    y0 = aes_mul4(temp[1 + j * 4] ^ temp[3 + j * 4]);
    y1 = aes_mul4(temp[0 + j * 4] ^ temp[2 + j * 4]);
    y2 = aes_mul2(y1 ^ y0);

    z0 = y2 ^ y0;
    z1 = y2 ^ y1;

    state[0 + j * 4] ^= z1;
    state[1 + j * 4] ^= z0;
    state[2 + j * 4] ^= z1;
    state[3 + j * 4] ^= z0;
  }

  return;
}

void aes_key_expand(unsigned char *round_key, unsigned char *key, int key_len,
                    unsigned char *rcon, int rnd) {
  // NOTE: The "words" of the key corresponds to columns of the key matrix,
  // i.e., word w[0] = [k[0], k[1], k[2], k[3]]

  // NOTE: round_key is the Nb words key used in the next round,
  //       key is the KEY_LEN last key bytes used to compute the new round key
  //       for key_len == 16, key == round_key

  unsigned char temp[4];
  unsigned char *old_key;
  old_key = (unsigned char *)malloc(key_len * sizeof(unsigned char));
  if (!old_key) {
    printf("ERROR: malloc() failed.");
  }

  // copy key to temp
  for (int i = 0; i < key_len; i++) {
    old_key[i] = key[i];
  }

  if (key_len == 16) {
    // shift last word
    temp[0] = old_key[13];
    temp[1] = old_key[14];
    temp[2] = old_key[15];
    temp[3] = old_key[12];

    // sub bytes in last word
    for (int i = 0; i < 4; i++) {
      temp[i] = sbox[temp[i]];
    }

    // update rcon
    aes_rcon_next(rcon);

    // get new words
    // Word 0
    key[0] = temp[0] ^ old_key[0] ^ *rcon;
    key[1] = temp[1] ^ old_key[1];
    key[2] = temp[2] ^ old_key[2];
    key[3] = temp[3] ^ old_key[3];

    // Word 1 - 3
    for (int i = 1; i < 4; i++) {
      key[0 + 4 * i] = key[0 + 4 * (i - 1)] ^ old_key[0 + 4 * i];
      key[1 + 4 * i] = key[1 + 4 * (i - 1)] ^ old_key[1 + 4 * i];
      key[2 + 4 * i] = key[2 + 4 * (i - 1)] ^ old_key[2 + 4 * i];
      key[3 + 4 * i] = key[3 + 4 * (i - 1)] ^ old_key[3 + 4 * i];
    }
  } else if (key_len == 24) {
    // determine shift (in bytes) and amount of key bytes to take over
    int shift, take;
    if (rnd == 0) {
      shift = 8;
      take = 16;
    } else {
      shift = 16;
      take = 8;
    }

    // copy to key what won't be changed in this round
    for (int i = 0; i < take; i++) {
      key[i] = old_key[shift + i];
    }

    // compute new bytes/words - there are four different cases:
    // 1. Word 6*,  7:           w/  RotWord, SubWord, Rcon - rnd 0
    // 2. Word 8,   9,  10,  11:                            - rnd 1, 4, 7, 10
    // 3. Word 12*, 13, 14,  15: w/  Rotword, SubWord, Rcon - rnd 2, 5, 8, 11
    // 4. Word 16,  17, 18*, 19: w/  RotWord, SubWord, Rcon - rnd 3, 6, 9
    if (rnd == 0) {
      // RotWord
      temp[0] = old_key[21];
      temp[1] = old_key[22];
      temp[2] = old_key[23];
      temp[3] = old_key[20];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_next(rcon);

      // Word 6
      key[16] = old_key[0] ^ temp[0] ^ *rcon;
      key[17] = old_key[1] ^ temp[1];
      key[18] = old_key[2] ^ temp[2];
      key[19] = old_key[3] ^ temp[3];

      // Word 7
      key[20] = old_key[4] ^ key[16];
      key[21] = old_key[5] ^ key[17];
      key[22] = old_key[6] ^ key[18];
      key[23] = old_key[7] ^ key[19];
    } else if (rnd == 1 || rnd == 4 || rnd == 7 || rnd == 10) {
      // Word 8
      key[8] = old_key[0] ^ key[4];   // key[4] == old_key[20]
      key[9] = old_key[1] ^ key[5];   // key[5] == old_key[21]
      key[10] = old_key[2] ^ key[6];  // key[6] == old_key[22]
      key[11] = old_key[3] ^ key[7];  // key[7] == old_key[23]

      // Word 9
      key[12] = old_key[4] ^ key[8];
      key[13] = old_key[5] ^ key[9];
      key[14] = old_key[6] ^ key[10];
      key[15] = old_key[7] ^ key[11];

      // Word 10
      key[16] = old_key[8] ^ key[12];
      key[17] = old_key[9] ^ key[13];
      key[18] = old_key[10] ^ key[14];
      key[19] = old_key[11] ^ key[15];

      // Word 11
      key[20] = old_key[12] ^ key[16];
      key[21] = old_key[13] ^ key[17];
      key[22] = old_key[14] ^ key[18];
      key[23] = old_key[15] ^ key[19];
    } else if (rnd == 2 || rnd == 5 || rnd == 8 || rnd == 11) {
      // RotWord
      temp[0] = old_key[21];
      temp[1] = old_key[22];
      temp[2] = old_key[23];
      temp[3] = old_key[20];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_next(rcon);

      // Word 12
      key[8] = old_key[0] ^ temp[0] ^ *rcon;
      key[9] = old_key[1] ^ temp[1];
      key[10] = old_key[2] ^ temp[2];
      key[11] = old_key[3] ^ temp[3];

      // Word 13
      key[12] = old_key[4] ^ key[8];
      key[13] = old_key[5] ^ key[9];
      key[14] = old_key[6] ^ key[10];
      key[15] = old_key[7] ^ key[11];

      // Word 14
      key[16] = old_key[8] ^ key[12];
      key[17] = old_key[9] ^ key[13];
      key[18] = old_key[10] ^ key[14];
      key[19] = old_key[11] ^ key[15];

      // Word 15
      key[20] = old_key[12] ^ key[16];
      key[21] = old_key[13] ^ key[17];
      key[22] = old_key[14] ^ key[18];
      key[23] = old_key[15] ^ key[19];
    } else {  // (rnd == 3 || rnd == 6 || rnd == 9 || rnd == 12)

      // Word 16
      key[8] = old_key[0] ^ key[4];   // key[4] == old_key[20]
      key[9] = old_key[1] ^ key[5];   // key[5] == old_key[21]
      key[10] = old_key[2] ^ key[6];  // key[6] == old_key[22]
      key[11] = old_key[3] ^ key[7];  // key[7] == old_key[23]

      // Word 17
      key[12] = old_key[4] ^ key[8];
      key[13] = old_key[5] ^ key[9];
      key[14] = old_key[6] ^ key[10];
      key[15] = old_key[7] ^ key[11];

      // RotWord
      temp[0] = key[13];
      temp[1] = key[14];
      temp[2] = key[15];
      temp[3] = key[12];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_next(rcon);

      // Word 18
      key[16] = old_key[8] ^ temp[0] ^ *rcon;
      key[17] = old_key[9] ^ temp[1];
      key[18] = old_key[10] ^ temp[2];
      key[19] = old_key[11] ^ temp[3];

      // Word 19
      key[20] = old_key[12] ^ key[16];
      key[21] = old_key[13] ^ key[17];
      key[22] = old_key[14] ^ key[18];
      key[23] = old_key[15] ^ key[19];
    }
  } else {  // key_len == 32

    // determine shift (in bytes) and amount of key bytes to take over
    int shift, take;
    if (rnd == 0) {
      shift = 0;
      take = 32;
    } else {
      shift = 16;
      take = 16;
    }

    // copy to key what won't be changed in this round
    for (int i = 0; i < take; i++) {
      key[i] = old_key[shift + i];
    }

    // compute new bytes/words - there three two cases
    // 1. Rnd 0:       DO NOTHING YET
    // 2. Odd  rounds: -> RotWord, SubWord, Rcon
    // 3. Even rounds: -> SubWord only

    if (rnd == 0) {
      // NOTHING TO COMPUTE
    } else if (rnd % 2) {  // odd rounds -> SubWord, RotWord, Rcon

      // RotWord
      temp[0] = old_key[29];
      temp[1] = old_key[30];
      temp[2] = old_key[31];
      temp[3] = old_key[28];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_next(rcon);

      // Word 8
      key[16] = old_key[0] ^ temp[0] ^ *rcon;
      key[17] = old_key[1] ^ temp[1];
      key[18] = old_key[2] ^ temp[2];
      key[19] = old_key[3] ^ temp[3];

      // Word 9
      key[20] = old_key[4] ^ key[16];
      key[21] = old_key[5] ^ key[17];
      key[22] = old_key[6] ^ key[18];
      key[23] = old_key[7] ^ key[19];

      // Word 10
      key[24] = old_key[8] ^ key[20];
      key[25] = old_key[9] ^ key[21];
      key[26] = old_key[10] ^ key[22];
      key[27] = old_key[11] ^ key[23];

      // Word 11
      key[28] = old_key[12] ^ key[24];
      key[29] = old_key[13] ^ key[25];
      key[30] = old_key[14] ^ key[26];
      key[31] = old_key[15] ^ key[27];
    } else {  // even rounds -> SubWord only

      // Extract
      temp[0] = old_key[28];
      temp[1] = old_key[29];
      temp[2] = old_key[30];
      temp[3] = old_key[31];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // Word 8
      key[16] = old_key[0] ^ temp[0];
      key[17] = old_key[1] ^ temp[1];
      key[18] = old_key[2] ^ temp[2];
      key[19] = old_key[3] ^ temp[3];

      // Word 9
      key[20] = old_key[4] ^ key[16];
      key[21] = old_key[5] ^ key[17];
      key[22] = old_key[6] ^ key[18];
      key[23] = old_key[7] ^ key[19];

      // Word 10
      key[24] = old_key[8] ^ key[20];
      key[25] = old_key[9] ^ key[21];
      key[26] = old_key[10] ^ key[22];
      key[27] = old_key[11] ^ key[23];

      // Word 11
      key[28] = old_key[12] ^ key[24];
      key[29] = old_key[13] ^ key[25];
      key[30] = old_key[14] ^ key[26];
      key[31] = old_key[15] ^ key[27];
    }
  }

  // copy 16 last bytes from key to round key
  for (int i = 0; i < 16; i++) {
    round_key[i] = key[key_len - 16 + i];
  }

  free(old_key);

  return;
}

void aes_inv_key_expand(unsigned char *round_key, unsigned char *key,
                        int key_len, unsigned char *rcon, int rnd) {
  // NOTE: The "words" of the key corresponds to columns of the key matrix,
  // i.e., word w[0] = [k[0], k[1], k[2], k[3]]

  // NOTE: round_key is the Nb words key used in the next round,
  //       key is the KEY_LEN last key bytes used to compute the new round key
  //       for key_len == 16, key == round_key

  unsigned char temp[4];
  unsigned char *old_key;
  old_key = (unsigned char *)malloc(key_len * sizeof(unsigned char));
  if (!old_key) {
    printf("ERROR: malloc() failed.");
  }

  // copy key to temp
  for (int i = 0; i < key_len; i++) {
    old_key[i] = key[i];
  }

  if (key_len == 16) {
    // get Word 3'-1':
    // Word 3' = Word 2 xor Word 3
    // Word 2' = Word 1 xor Word 2
    // Word 1' = Word 0 xor Word 1
    for (int i = 3; i > 0; i--) {
      key[0 + 4 * i] = old_key[0 + 4 * (i - 1)] ^ old_key[0 + 4 * i];
      key[1 + 4 * i] = old_key[1 + 4 * (i - 1)] ^ old_key[1 + 4 * i];
      key[2 + 4 * i] = old_key[2 + 4 * (i - 1)] ^ old_key[2 + 4 * i];
      key[3 + 4 * i] = old_key[3 + 4 * (i - 1)] ^ old_key[3 + 4 * i];
    }

    // update rcon
    aes_rcon_prev(rcon, key_len);

    // get Word 0':
    // 1. temp    = Word 3' -> shift, aes_inv_sub_bytes
    // 2. Word 0' = (temp xor Word 0) xor rcon

    // shift Word 3'
    temp[0] = key[13];
    temp[1] = key[14];
    temp[2] = key[15];
    temp[3] = key[12];

    // sub bytes shifted Word 3'
    for (int i = 0; i < 4; i++) {
      temp[i] = sbox[temp[i]];
    }

    // get Word 0': (temp xor Word 0) xor rcon
    key[0] = temp[0] ^ old_key[0] ^ *rcon;
    key[1] = temp[1] ^ old_key[1];
    key[2] = temp[2] ^ old_key[2];
    key[3] = temp[3] ^ old_key[3];
  } else if (key_len == 24) {
    // determine shift (in bytes) and amount of key bytes to take over
    int shift, take;
    if (rnd == 0) {
      shift = 8;
      take = 16;
    } else {
      shift = 16;
      take = 8;
    }

    // copy to key what won't be changed in this round - going backwards
    for (int i = take + shift - 1; i >= shift; i--) {
      key[i] = old_key[i - shift];
    }

    // compute new bytes/words - there are four different cases:
    // 1. Word 44,  45:                                     - rnd 0
    // 2. Word 40,  41, 42*, 43: w/  Rotword, SubWord, Rcon - rnd 1, 4, 7, 10
    // 3. Word 36*, 37, 38,  39: w/  Rotword, SubWord, Rcon - rnd 2, 5, 8, 11
    // 4. Word 32,  33, 34,  35:                            - rnd 3, 6, 9
    if (rnd == 0) {
      // Word 45 = Word 50 xor Word 51
      key[4] = old_key[20] ^ old_key[16];
      key[5] = old_key[21] ^ old_key[17];
      key[6] = old_key[22] ^ old_key[18];
      key[7] = old_key[23] ^ old_key[19];

      // Word 44 = Word 49 xor Word 50
      key[0] = old_key[16] ^ old_key[12];
      key[1] = old_key[17] ^ old_key[13];
      key[2] = old_key[18] ^ old_key[14];
      key[3] = old_key[19] ^ old_key[15];
    } else if (rnd == 1 || rnd == 4 || rnd == 7 || rnd == 10) {
      // Word 43
      key[12] = old_key[20] ^ old_key[16];
      key[13] = old_key[21] ^ old_key[17];
      key[14] = old_key[22] ^ old_key[18];
      key[15] = old_key[23] ^ old_key[19];

      // RotWord
      temp[0] = old_key[13];
      temp[1] = old_key[14];
      temp[2] = old_key[15];
      temp[3] = old_key[12];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_prev(rcon, key_len);

      // Word 42
      key[8] = old_key[16] ^ temp[0] ^ *rcon;
      key[9] = old_key[17] ^ temp[1];
      key[10] = old_key[18] ^ temp[2];
      key[11] = old_key[19] ^ temp[3];

      // Word 41
      key[4] = old_key[12] ^ old_key[8];
      key[5] = old_key[13] ^ old_key[9];
      key[6] = old_key[14] ^ old_key[10];
      key[7] = old_key[15] ^ old_key[11];

      // Word 40
      key[0] = old_key[8] ^ old_key[4];
      key[1] = old_key[9] ^ old_key[5];
      key[2] = old_key[10] ^ old_key[6];
      key[3] = old_key[11] ^ old_key[7];
    } else if (rnd == 2 || rnd == 5 || rnd == 8 || rnd == 11) {
      // Word 39
      key[12] = old_key[20] ^ old_key[16];
      key[13] = old_key[21] ^ old_key[17];
      key[14] = old_key[22] ^ old_key[18];
      key[15] = old_key[23] ^ old_key[19];

      // Word 38
      key[8] = old_key[16] ^ old_key[12];
      key[9] = old_key[17] ^ old_key[13];
      key[10] = old_key[18] ^ old_key[14];
      key[11] = old_key[19] ^ old_key[15];

      // Word 37
      key[4] = old_key[12] ^ old_key[8];
      key[5] = old_key[13] ^ old_key[9];
      key[6] = old_key[14] ^ old_key[10];
      key[7] = old_key[15] ^ old_key[11];

      // RotWord
      temp[0] = old_key[5];
      temp[1] = old_key[6];
      temp[2] = old_key[7];
      temp[3] = old_key[4];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_prev(rcon, key_len);

      // Word 36
      key[0] = old_key[8] ^ temp[0] ^ *rcon;
      key[1] = old_key[9] ^ temp[1];
      key[2] = old_key[10] ^ temp[2];
      key[3] = old_key[11] ^ temp[3];
    } else {  // (rnd == 3 || rnd == 6 || rnd == 9 || rnd == 12)

      // Word 35
      key[12] = old_key[20] ^ old_key[16];
      key[13] = old_key[21] ^ old_key[17];
      key[14] = old_key[22] ^ old_key[18];
      key[15] = old_key[23] ^ old_key[19];

      // Word 34
      key[8] = old_key[16] ^ old_key[12];
      key[9] = old_key[17] ^ old_key[13];
      key[10] = old_key[18] ^ old_key[14];
      key[11] = old_key[19] ^ old_key[15];

      // Word 33
      key[4] = old_key[12] ^ old_key[8];
      key[5] = old_key[13] ^ old_key[9];
      key[6] = old_key[14] ^ old_key[10];
      key[7] = old_key[15] ^ old_key[11];

      // Word 32
      key[0] = old_key[8] ^ old_key[4];
      key[1] = old_key[9] ^ old_key[5];
      key[2] = old_key[10] ^ old_key[6];
      key[3] = old_key[11] ^ old_key[7];
    }
  } else {  // key_len == 32

    // determine shift (in bytes) and amount of key bytes to take over
    int shift, take;
    if (rnd == 0) {
      shift = 0;
      take = 32;
    } else {
      shift = 16;
      take = 16;
    }

    // copy to key what won't be changed in this round - going backwards
    for (int i = take + shift - 1; i >= shift; i--) {
      key[i] = old_key[i - shift];
    }

    // compute new bytes/words - there are three cases
    // 1. Rnd 0:       DO NOTHING YET
    // 2. Odd  rounds: -> RotWord, SubWord, Rcon
    // 3. Even rounds: -> SubWord only

    if (rnd == 0) {
      // NOTHING TO COMPUTE
    } else if (rnd % 2) {  // odd rounds -> SubWord, RotWord, Rcon

      // Word 51
      key[12] = old_key[28] ^ old_key[24];
      key[13] = old_key[29] ^ old_key[25];
      key[14] = old_key[30] ^ old_key[26];
      key[15] = old_key[31] ^ old_key[27];

      // Word 50
      key[8] = old_key[24] ^ old_key[20];
      key[9] = old_key[25] ^ old_key[21];
      key[10] = old_key[26] ^ old_key[22];
      key[11] = old_key[27] ^ old_key[23];

      // Word 49
      key[4] = old_key[20] ^ old_key[16];
      key[5] = old_key[21] ^ old_key[17];
      key[6] = old_key[22] ^ old_key[18];
      key[7] = old_key[23] ^ old_key[19];

      // RotWord
      temp[0] = old_key[13];
      temp[1] = old_key[14];
      temp[2] = old_key[15];
      temp[3] = old_key[12];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // update rcon
      aes_rcon_prev(rcon, key_len);

      // Word 48
      key[0] = old_key[16] ^ temp[0] ^ *rcon;
      key[1] = old_key[17] ^ temp[1];
      key[2] = old_key[18] ^ temp[2];
      key[3] = old_key[19] ^ temp[3];
    } else {  // even rounds -> SubWord only

      // Word 47
      key[12] = old_key[28] ^ old_key[24];
      key[13] = old_key[29] ^ old_key[25];
      key[14] = old_key[30] ^ old_key[26];
      key[15] = old_key[31] ^ old_key[27];

      // Word 46
      key[8] = old_key[24] ^ old_key[20];
      key[9] = old_key[25] ^ old_key[21];
      key[10] = old_key[26] ^ old_key[22];
      key[11] = old_key[27] ^ old_key[23];

      // Word 45
      key[4] = old_key[20] ^ old_key[16];
      key[5] = old_key[21] ^ old_key[17];
      key[6] = old_key[22] ^ old_key[18];
      key[7] = old_key[23] ^ old_key[19];

      // Extract
      temp[0] = old_key[12];
      temp[1] = old_key[13];
      temp[2] = old_key[14];
      temp[3] = old_key[15];

      // SubWord
      for (int i = 0; i < 4; i++) {
        temp[i] = sbox[temp[i]];
      }

      // Word 44
      key[0] = old_key[16] ^ temp[0];
      key[1] = old_key[17] ^ temp[1];
      key[2] = old_key[18] ^ temp[2];
      key[3] = old_key[19] ^ temp[3];
    }
  }

  // copy 16 first bytes from key to round key
  for (int i = 0; i < 16; i++) {
    round_key[i] = key[i];
  }

  free(old_key);

  return;
}

void aes_rcon_next(unsigned char *rcon) {
  // rcon cannot be 0
  if (*rcon) {
    // update rcon
    *rcon = aes_mul2(*rcon);
  } else {
    // init rcon to first round value
    *rcon = 0x1;
  }

  return;
}

void aes_rcon_prev(unsigned char *rcon, int key_len) {
  unsigned char rcon_tmp;

  // rcon cannot be 0
  if (*rcon) {
    // update rcon - actually this is the inverse of aes_mul2
    rcon_tmp = *rcon;

    // set individual bits of rcon
    *rcon = 0x0;
    //            extract bits             possible xor      shift to right
    //            position
    *rcon |= (((rcon_tmp >> 1) & 0x1) ^ ((rcon_tmp >> 0) & 0x1)) << 0;
    *rcon |= (((rcon_tmp >> 2) & 0x1)) << 1;
    *rcon |= (((rcon_tmp >> 3) & 0x1) ^ ((rcon_tmp >> 0) & 0x1)) << 2;
    *rcon |= (((rcon_tmp >> 4) & 0x1) ^ ((rcon_tmp >> 0) & 0x1)) << 3;
    *rcon |= (((rcon_tmp >> 5) & 0x1)) << 4;
    *rcon |= (((rcon_tmp >> 6) & 0x1)) << 5;
    *rcon |= (((rcon_tmp >> 7) & 0x1)) << 6;
    *rcon |= (((rcon_tmp >> 0) & 0x1)) << 7;
  } else {
    // init rcon to first round value
    if (key_len == 16) {
      *rcon = 0x36;
    } else if (key_len == 24) {
      *rcon = 0x80;
    } else {  // key_len == 32
      *rcon = 0x40;
    }
  }

  return;
}
