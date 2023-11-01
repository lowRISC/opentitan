// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
/**
 * NOTE: The only intended use of this code is to serve as a PRNG for generating
 * input data for SCA experiments and penetration testing.
 * The library is not hardened against any type of attacks, and it should not be
 * used for any purpose other than stated.
 *
 * During the SCA experiments, encryptions are verified on the host side by
 * running the same encryption using PyCryptodome package and comparing the
 * result.
 *
 * Implementation of round-functions is based on a transposed-state technique
 * for 32-bit architecture presented in:
 *
 * [1] Bertoni et. al., Efficient Software Implementation of AES on 32-Bit
 *     Platforms, CHES 2002.
 *
 *     https://link.springer.com/content/pdf/10.1007/3-540-36400-5_13.pdf
 *
 */
#include "aes.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "sw/device/lib/base/memory.h"

enum {
  kAesNumRounds = 10,
  kAesNumKeyBytes = 16,
  kAesNumTextBytes = 16,
  kAesNumStateBytes = 16,
  kAesNumStateWords = 4
};

static void aes_add_round_key(uint32_t *state, const uint32_t *round_key) {
  state[0] ^= round_key[0];
  state[1] ^= round_key[1];
  state[2] ^= round_key[2];
  state[3] ^= round_key[3];
}

static void aes_sub_bytes(uint32_t *state) {
  // SubBytes on a transposed state
  // Section 3.1 of [1]
  for (size_t i = 0; i < 4; ++i) {
    state[i] = (uint32_t)kSbox[state[i] & 0xff] |
               ((uint32_t)kSbox[(state[i] >> 8) & 0xff] << 8) |
               ((uint32_t)kSbox[(state[i] >> 16) & 0xff] << 16) |
               ((uint32_t)kSbox[(state[i] >> 24) & 0xff] << 24);
  }
}

static uint32_t aes_mul2(uint32_t s) {
  // Multiplication by 2 in Rijndael field.
  // Each byte of the 32b input word is multiplied.
  uint32_t t;
  t = (uint32_t)kMul2[s & 0xff] | ((uint32_t)kMul2[(s >> 8) & 0xff] << 8) |
      ((uint32_t)kMul2[(s >> 16) & 0xff] << 16) |
      ((uint32_t)kMul2[(s >> 24) & 0xff] << 24);
  return t;
}

static void aes_shift_rows(uint32_t *state) {
  // ShiftRows on a transposed state
  // Section 3.1 of [1]
  state[1] = (state[1] >> 8) | (state[1] << 24);
  state[2] = (state[2] >> 16) | (state[2] << 16);
  state[3] = (state[3] >> 24) | (state[3] << 8);
}

static void aes_mix_columns(uint32_t *state) {
  // MixColumns on a transposed state
  // Section 3.1 of [1]
  uint32_t temp[kAesNumStateWords];

  memcpy(temp, state, kAesNumStateBytes);

  state[0] = temp[1] ^ temp[2] ^ temp[3];
  state[1] = temp[0] ^ temp[2] ^ temp[3];
  state[2] = temp[0] ^ temp[1] ^ temp[3];
  state[3] = temp[0] ^ temp[1] ^ temp[2];

  temp[0] = aes_mul2(temp[0]);
  temp[1] = aes_mul2(temp[1]);
  temp[2] = aes_mul2(temp[2]);
  temp[3] = aes_mul2(temp[3]);

  state[0] ^= temp[0] ^ temp[1];
  state[1] ^= temp[1] ^ temp[2];
  state[2] ^= temp[2] ^ temp[3];
  state[3] ^= temp[3] ^ temp[0];
}

static void aes_transpose_to_32(uint8_t *in_data, uint32_t *out_data) {
  out_data[0] = (uint32_t)in_data[0] | ((uint32_t)in_data[4] << 8) |
                ((uint32_t)in_data[8] << 16) | ((uint32_t)in_data[12] << 24);
  out_data[1] = (uint32_t)in_data[1] | ((uint32_t)in_data[5] << 8) |
                ((uint32_t)in_data[9] << 16) | ((uint32_t)in_data[13] << 24);
  out_data[2] = (uint32_t)in_data[2] | ((uint32_t)in_data[6] << 8) |
                ((uint32_t)in_data[10] << 16) | ((uint32_t)in_data[14] << 24);
  out_data[3] = (uint32_t)in_data[3] | ((uint32_t)in_data[7] << 8) |
                ((uint32_t)in_data[11] << 16) | ((uint32_t)in_data[15] << 24);
}

static void aes_transpose_from_32(uint32_t *in_data, uint8_t *out_data) {
  out_data[0] = (uint8_t)(in_data[0] & 0xff);
  out_data[1] = (uint8_t)(in_data[1] & 0xff);
  out_data[2] = (uint8_t)(in_data[2] & 0xff);
  out_data[3] = (uint8_t)(in_data[3] & 0xff);
  out_data[4] = (uint8_t)(in_data[0] >> 8) & 0xff;
  out_data[5] = (uint8_t)(in_data[1] >> 8) & 0xff;
  out_data[6] = (uint8_t)(in_data[2] >> 8) & 0xff;
  out_data[7] = (uint8_t)(in_data[3] >> 8) & 0xff;
  out_data[8] = (uint8_t)(in_data[0] >> 16) & 0xff;
  out_data[9] = (uint8_t)(in_data[1] >> 16) & 0xff;
  out_data[10] = (uint8_t)(in_data[2] >> 16) & 0xff;
  out_data[11] = (uint8_t)(in_data[3] >> 16) & 0xff;
  out_data[12] = (uint8_t)(in_data[0] >> 24) & 0xff;
  out_data[13] = (uint8_t)(in_data[1] >> 24) & 0xff;
  out_data[14] = (uint8_t)(in_data[2] >> 24) & 0xff;
  out_data[15] = (uint8_t)(in_data[3] >> 24) & 0xff;
}

static uint8_t aes_rcon_next(uint8_t rcon) {
  // rcon cannot be 0
  if (rcon != 0) {
    // update round constant
    return kMul2[rcon];
  } else {
    // init round constant to first-round value
    return 0x1;
  }
}

static void aes_key_expand(uint8_t *round_key, uint8_t *rcon) {
  uint8_t temp[kAesNumStateWords];
  uint8_t old_key[kAesNumKeyBytes];

  // copy key to temp
  memcpy(old_key, round_key, kAesNumKeyBytes);

  // shift last word
  temp[0] = old_key[13];
  temp[1] = old_key[14];
  temp[2] = old_key[15];
  temp[3] = old_key[12];

  // sub bytes in last word
  temp[0] = kSbox[temp[0]];
  temp[1] = kSbox[temp[1]];
  temp[2] = kSbox[temp[2]];
  temp[3] = kSbox[temp[3]];

  // update rcon
  *rcon = aes_rcon_next(*rcon);

  // get new words
  round_key[0] = temp[0] ^ old_key[0] ^ *rcon;
  round_key[1] = temp[1] ^ old_key[1];
  round_key[2] = temp[2] ^ old_key[2];
  round_key[3] = temp[3] ^ old_key[3];

  for (size_t i = 4; i < kAesNumKeyBytes; ++i) {
    round_key[i] = round_key[i - 4] ^ old_key[i];
  }
}

void aes_key_schedule(uint32_t *round_keys, const uint8_t *key) {
  // Derives all round keys for AES128
  // Each key is storred in 4 32-bit words in a transposed-state form.
  uint8_t rcon = 0;
  uint8_t key_temp[kAesNumKeyBytes];
  uint32_t key_temp_32[kAesNumStateWords];

  memcpy(key_temp, key, kAesNumKeyBytes);
  aes_transpose_to_32(key_temp, key_temp_32);
  memcpy(round_keys, key_temp_32, kAesNumKeyBytes);
  for (size_t i = 1; i < kAesNumRounds + 1; ++i) {
    aes_key_expand(key_temp, &rcon);
    aes_transpose_to_32(key_temp, key_temp_32);
    memcpy(round_keys + i * kAesNumStateWords, key_temp_32, kAesNumKeyBytes);
  }
}

void aes_sw_encrypt_block(const uint8_t *plain_text, const uint32_t *round_keys,
                          uint8_t *cipher_text) {
  uint32_t state[kAesNumStateWords];

  // initially transpose state
  uint8_t pt[kAesNumTextBytes];
  memcpy(pt, plain_text, kAesNumTextBytes);
  aes_transpose_to_32(pt, state);

  // encrypt
  aes_add_round_key(state, round_keys);
  for (int j = 0; j < kAesNumRounds - 1; ++j) {
    aes_sub_bytes(state);
    aes_shift_rows(state);
    aes_mix_columns(state);
    aes_add_round_key(state, round_keys + (j + 1) * kAesNumStateWords);
  }
  aes_sub_bytes(state);
  aes_shift_rows(state);
  aes_add_round_key(state, round_keys + kAesNumStateWords * kAesNumRounds);

  // transpose the result back into the byte form
  aes_transpose_from_32(state, cipher_text);
}
