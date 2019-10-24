// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"

#include "aes_regs.h"  // Generated.
#include "sw/device/lib/common.h"

#define AES0_BASE_ADDR 0x40110000
#define AES_NUM_REGS_DATA 4
#define AES_NUM_REGS_KEY 8

void aes_init(aes_cfg_t aes_cfg) {
  REG32(AES_CTRL(0)) =
      (aes_cfg.mode << AES_CTRL_MODE) |
      ((aes_cfg.key_len & AES_CTRL_KEY_LEN_MASK) << AES_CTRL_KEY_LEN_OFFSET) |
      (aes_cfg.manual_start_trigger << AES_CTRL_MANUAL_START_TRIGGER) |
      (aes_cfg.force_data_overwrite << AES_CTRL_FORCE_DATA_OVERWRITE);
};

void aes_key_put(const void *key, aes_key_len_t key_len) {
  // Determine how many key registers to use.
  size_t num_regs_key_used;
  if (key_len == kAes256) {
    num_regs_key_used = 8;
  } else if (key_len == kAes192) {
    num_regs_key_used = 6;
  } else {
    num_regs_key_used = 4;
  }

  // Write the used key registers.
  for (int i = 0; i < num_regs_key_used; ++i) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = ((uint32_t *)key)[i];
  }
  // Write the unused key registers (the AES unit requires all key registers to
  // be written).
  for (int i = num_regs_key_used; i < AES_NUM_REGS_KEY; ++i) {
    REG32(AES_KEY0(0) + i * sizeof(uint32_t)) = 0x0;
  }
}

void aes_data_put_wait(const void *data) {
  // Wait for AES unit to be ready for new input data.
  while (!aes_data_ready()) {
  }

  // Provide the input data.
  aes_data_put(data);
}

void aes_data_put(const void *data) {
  // Write the four input data registers.
  for (int i = 0; i < AES_NUM_REGS_DATA; ++i) {
    REG32(AES_DATA_IN0(0) + i * sizeof(uint32_t)) = ((uint32_t *)data)[i];
  }
}

void aes_data_get_wait(void *data) {
  // Wait for AES unit to have valid output data.
  while (!aes_data_valid()) {
  }

  // Get the data.
  aes_data_get(data);
}

void aes_data_get(void *data) {
  // Read the four output data registers.
  for (int i = 0; i < AES_NUM_REGS_DATA; ++i) {
    ((uint32_t *)data)[i] = REG32(AES_DATA_OUT0(0) + i * sizeof(uint32_t));
  }
}

bool aes_data_ready(void) {
  return (REG32(AES_STATUS(0)) & (0x1u << AES_STATUS_INPUT_READY));
}

bool aes_data_valid(void) {
  return (REG32(AES_STATUS(0)) & (0x1u << AES_STATUS_OUTPUT_VALID));
}

bool aes_idle(void) {
  return (REG32(AES_STATUS(0)) & (0x1u << AES_STATUS_IDLE));
}

void aes_clear(void) {
  // Wait for AES unit to be idle.
  while (!aes_idle()) {
  }

  // Disable autostart
  REG32(AES_CTRL(0)) = 0x1u << AES_CTRL_MANUAL_START_TRIGGER;

  // Clear internal key and output registers
  REG32(AES_TRIGGER(0)) = (0x1u << AES_TRIGGER_KEY_CLEAR) |
                          (0x1u << AES_TRIGGER_DATA_IN_CLEAR) |
                          (0x1u << AES_TRIGGER_DATA_OUT_CLEAR);

  // Wait for output not valid, and input ready
  while (!(!aes_data_valid() && aes_data_ready())) {
  }
}
