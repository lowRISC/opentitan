// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "aes.h"

#include "aes_regs.h"
#include "common.h"

#define AES0_BASE_ADDR 0x40110000

void aes_init(const aes_cfg_t aes_cfg) {
  // convert key_len from bytes to onehot
  size_t key_len_onehot = 0b001;
  if (aes_cfg.key_len_in_bytes == 24) {
    key_len_onehot = 0b010;
  } else if (aes_cfg.key_len_in_bytes == 32) {
    key_len_onehot = 0b100;
  }

  REG32(AES_CTRL(0)) =
      aes_cfg.mode << AES_CTRL_MODE |
      (key_len_onehot & AES_CTRL_KEY_LEN_MASK) << AES_CTRL_KEY_LEN_OFFSET |
      aes_cfg.manual_start_trigger << AES_CTRL_MANUAL_START_TRIGGER |
      aes_cfg.force_data_overwrite << AES_CTRL_FORCE_DATA_OVERWRITE;
  return;
};

void aes_key_put(const void *key, const size_t key_len_in_bytes) {
  const size_t key_len_in_words = key_len_in_bytes >> 2;

  for (int i = 0; i < key_len_in_words; i++) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = ((uint32_t *)key)[i];
  }
  for (int i = key_len_in_words; i < 8; i++) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = 0x0;
  }

  return;
}

void aes_data_put_wait(const void *data) {
  // wait for input being ready
  aes_data_ready();

  // put the data
  aes_data_put(data);

  return;
}

void aes_data_put(const void *data) {
  for (int i = 0; i < 4; i++) {
    REG32(AES_DATA_IN0(0) + i * sizeof(uint32_t)) = ((uint32_t *)data)[i];
  }

  return;
}

void aes_data_get_wait(void *data) {
  // wait for data to be valid
  aes_data_valid();

  // get the data
  aes_data_get(data);

  return;
}

void aes_data_get(void *data) {
  for (int i = 0; i < 4; i++) {
    ((uint32_t *)data)[i] = REG32(AES_DATA_OUT0(0) + i * sizeof(uint32_t));
  }

  return;
}

void aes_data_ready(void) {
  while (!((REG32(AES_STATUS(0)) >> AES_STATUS_INPUT_READY) & 0x1)) {
  }
  return;
}

void aes_data_valid(void) {
  while (!((REG32(AES_STATUS(0)) >> AES_STATUS_OUTPUT_VALID) & 0x1)) {
  }
  return;
}

void aes_idle(void) {
  while (!((REG32(AES_STATUS(0)) >> AES_STATUS_IDLE) & 0x1)) {
  }
  return;
}

void aes_clear(void) {
  // Wait for idle
  aes_idle();

  // Disable autostart
  REG32(AES_CTRL(0)) = 0x1 << AES_CTRL_MANUAL_START_TRIGGER;

  // Clear input data registers
  for (int i = 0; i < 4; i++) {
    REG32(AES_DATA_IN0(0) + i * sizeof(uint32_t)) = 0x0;
  }

  // Clear initial key registers
  for (int i = 0; i < 4; i++) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = 0x0;
  }

  // Clear internal key and output registers
  REG32(AES_TRIGGER(0)) =
      (0x1 << AES_TRIGGER_KEY_CLEAR) | (0x1 << AES_TRIGGER_DATA_OUT_CLEAR);

  // Wait for output not valid, and input ready
  uint32_t status = (0x1 << AES_STATUS_OUTPUT_VALID);
  while (((status >> AES_STATUS_OUTPUT_VALID) & 0x1) ||
         !((status >> AES_STATUS_INPUT_READY) & 0x1)) {
    status = REG32(AES_STATUS(0));
  }

  return;
}
