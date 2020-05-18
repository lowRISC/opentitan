// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "present.inc"
#include "svdpi.h"

typedef unsigned long long int ull_t;

// Helper function used only by this C file.
// Returns the key schedule corresponding to the input key.
uint64_t *get_key_schedule(uint64_t key_high, uint64_t key_low,
                           uint8_t num_rounds, uint8_t key_size_80) {
  return key_schedule(key_high, key_low, num_rounds, (_Bool)key_size_80, 0);
}

extern void c_dpi_key_schedule(uint64_t key_high, uint64_t key_low,
                               uint8_t num_rounds, uint8_t key_size_80,
                               svBitVecVal *key_array) {
  uint64_t *key_schedule = (uint64_t *)malloc(num_rounds * sizeof(uint64_t));
  uint64_t key;
  svBitVecVal key_hi;
  svBitVecVal key_lo;

  // get the key schedule from the C model
  key_schedule = get_key_schedule(key_high, key_low, num_rounds, key_size_80);

  // write the key schedule to simulation
  int i;
  for (i = 0; i < num_rounds; i++) {
    key = key_schedule[i];
    key_hi = (svBitVecVal)(key >> 32);
    key_lo = (svBitVecVal)(key & 0xFFFFFFFF);
    key_array[i * 2] = key_lo;
    key_array[i * 2 + 1] = key_hi;
  }

  // free allocated memory
  free(key_schedule);
}

extern uint64_t c_dpi_encrypt(uint64_t plaintext, uint64_t key_high,
                              uint64_t key_low, uint8_t num_rounds,
                              uint8_t key_size_80) {
  uint64_t encrypt_result;
  uint64_t *key_schedule = (uint64_t *)malloc(num_rounds * sizeof(uint64_t));

  key_schedule = get_key_schedule(key_high, key_low, num_rounds, key_size_80);
  encrypt_result = (uint64_t)encrypt(plaintext, key_schedule, num_rounds, 0);
  free(key_schedule);
  return encrypt_result;
}

extern uint64_t c_dpi_decrypt(uint64_t ciphertext, uint64_t key_high,
                              uint64_t key_low, uint8_t num_rounds,
                              uint8_t key_size_80) {
  uint64_t decrypt_result;
  uint64_t *key_schedule = (uint64_t *)malloc(sizeof(uint64_t));

  key_schedule = get_key_schedule(key_high, key_low, num_rounds, key_size_80);
  decrypt_result = (uint64_t)decrypt(ciphertext, key_schedule, num_rounds, 0);
  free(key_schedule);
  return decrypt_result;
}
