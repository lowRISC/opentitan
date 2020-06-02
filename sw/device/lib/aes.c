// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"

#include "aes_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// TODO:
// 1) Refactor to use use dif_aes.
// 2) Verify that test still works.
// 3) Use dif_aes directly in the test (probably remove this file).

#define AES0_BASE_ADDR TOP_EARLGREY_AES_BASE_ADDR
#define AES_NUM_REGS_KEY 8
#define AES_NUM_REGS_IV 4
#define AES_NUM_REGS_DATA 4

#define REG32(add) *((volatile uint32_t *)(add))

void aes_init(aes_cfg_t aes_cfg) {
  uint32_t cfg_val =
      (aes_cfg.operation << AES_CTRL_SHADOWED_OPERATION_BIT) |
      ((aes_cfg.mode & AES_CTRL_SHADOWED_MODE_MASK)
       << AES_CTRL_SHADOWED_MODE_OFFSET) |
      ((aes_cfg.key_len & AES_CTRL_SHADOWED_KEY_LEN_MASK)
       << AES_CTRL_SHADOWED_KEY_LEN_OFFSET) |
      (aes_cfg.manual_operation << AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT);
  REG32(AES0_BASE_ADDR + AES_CTRL_SHADOWED_REG_OFFSET) = cfg_val;
  REG32(AES0_BASE_ADDR + AES_CTRL_SHADOWED_REG_OFFSET) = cfg_val;
};

void aes_key_put(const void *key_share0, const void *key_share1,
                 aes_key_len_t key_len) {
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
    REG32(AES0_BASE_ADDR + AES_KEY_SHARE0_0_REG_OFFSET + i * sizeof(uint32_t)) =
        ((uint32_t *)key_share0)[i];
    REG32(AES0_BASE_ADDR + AES_KEY_SHARE1_0_REG_OFFSET + i * sizeof(uint32_t)) =
        ((uint32_t *)key_share1)[i];
  }
  // Write the unused key registers (the AES unit requires all key registers to
  // be written).
  for (int i = num_regs_key_used; i < AES_NUM_REGS_KEY; ++i) {
    REG32(AES0_BASE_ADDR + AES_KEY_SHARE0_0_REG_OFFSET + i * sizeof(uint32_t)) =
        0x0;
    REG32(AES0_BASE_ADDR + AES_KEY_SHARE1_0_REG_OFFSET + i * sizeof(uint32_t)) =
        0x0;
  }
}

void aes_iv_put(const void *iv) {
  // Write the four initialization vector registers.
  for (int i = 0; i < AES_NUM_REGS_IV; ++i) {
    REG32(AES0_BASE_ADDR + AES_IV_0_REG_OFFSET + i * sizeof(uint32_t)) =
        ((uint32_t *)iv)[i];
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
    REG32(AES0_BASE_ADDR + AES_DATA_IN_0_REG_OFFSET + i * sizeof(uint32_t)) =
        ((uint32_t *)data)[i];
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
    ((uint32_t *)data)[i] = REG32(AES0_BASE_ADDR + AES_DATA_OUT_0_REG_OFFSET +
                                  i * sizeof(uint32_t));
  }
}

bool aes_data_ready(void) {
  return (REG32(AES0_BASE_ADDR + AES_STATUS_REG_OFFSET) &
          (0x1u << AES_STATUS_INPUT_READY_BIT));
}

bool aes_data_valid(void) {
  return (REG32(AES0_BASE_ADDR + AES_STATUS_REG_OFFSET) &
          (0x1u << AES_STATUS_OUTPUT_VALID_BIT));
}

bool aes_idle(void) {
  return (REG32(AES0_BASE_ADDR + AES_STATUS_REG_OFFSET) &
          (0x1u << AES_STATUS_IDLE_BIT));
}

void aes_manual_trigger(void) {
  REG32(AES0_BASE_ADDR + AES_TRIGGER_REG_OFFSET) = 0x1u
                                                   << AES_TRIGGER_START_BIT;
}

void aes_clear(void) {
  // Wait for AES unit to be idle.
  while (!aes_idle()) {
  }

  // Disable autostart
  uint32_t cfg_val = 0x1u << AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT;
  REG32(AES0_BASE_ADDR + AES_CTRL_SHADOWED_REG_OFFSET) = cfg_val;
  REG32(AES0_BASE_ADDR + AES_CTRL_SHADOWED_REG_OFFSET) = cfg_val;

  // Clear internal key and output registers
  REG32(AES0_BASE_ADDR + AES_TRIGGER_REG_OFFSET) =
      (0x1u << AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT) |
      (0x1u << AES_TRIGGER_DATA_OUT_CLEAR_BIT);

  // Wait for output not valid, and input ready
  while (!(!aes_data_valid() && aes_data_ready())) {
  }
}
