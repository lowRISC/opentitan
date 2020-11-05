// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/hmac.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define HMAC0_BASE_ADDR TOP_EARLGREY_HMAC_BASE_ADDR
#define HMAC_FIFO_MAX 16
#define HMAC_FIFO_GROUP_SIZE HMAC_FIFO_MAX / 2

#define REG32(add) *((volatile uint32_t *)(add))

void hmac_init(hmac_cfg_t hmac_cfg) {
  REG32(HMAC0_BASE_ADDR + HMAC_CFG_REG_OFFSET) =
      hmac_cfg.input_endian_swap << HMAC_CFG_ENDIAN_SWAP_BIT |
      1 << hmac_cfg.mode |
      hmac_cfg.digest_endian_swap << HMAC_CFG_DIGEST_SWAP_BIT;
  for (int i = 0; i < 8; i++) {
    REG32(HMAC0_BASE_ADDR + HMAC_KEY_0_REG_OFFSET + i * sizeof(uint32_t)) =
        hmac_cfg.keys[i];
  }
  REG32(HMAC0_BASE_ADDR + HMAC_CMD_REG_OFFSET) = 1 << HMAC_CMD_HASH_START_BIT;
};

static int hmac_fifo_depth(void) {
  return (REG32(HMAC0_BASE_ADDR + HMAC_STATUS_REG_OFFSET) >>
          HMAC_STATUS_FIFO_DEPTH_OFFSET) &
         HMAC_STATUS_FIFO_DEPTH_MASK;
}

static int fifo_avail(void) { return HMAC_FIFO_MAX - hmac_fifo_depth(); }

void hmac_update(const void *data, size_t size_in_bytes) {
  const uint32_t *wp = (const uint32_t *)data;
  uint32_t bytes_per_word = sizeof(uint32_t) / sizeof(uint8_t);
  uint32_t bytes_left_over = (size_in_bytes % bytes_per_word);
  size_t words_remaining = size_in_bytes / bytes_per_word;

  // write in all words
  while (words_remaining > 0) {
    if (words_remaining > HMAC_FIFO_GROUP_SIZE) {
      // wait until FIFO is at least half drained
      while (fifo_avail() <= HMAC_FIFO_GROUP_SIZE) {
      }

      // write a whole group
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      words_remaining -= HMAC_FIFO_GROUP_SIZE;
    } else {
      REG32(HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *wp++;
      words_remaining--;
    };
  }

  const uint8_t *bp = (const uint8_t *)wp;
  for (; bytes_left_over > 0; --bytes_left_over) {
    *((volatile uint8_t *)HMAC0_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET) = *bp++;
  }
}

void hmac_done(uint32_t *digest) {
  REG32(HMAC0_BASE_ADDR + HMAC_CMD_REG_OFFSET) = 1 << HMAC_CMD_HASH_PROCESS_BIT;
  while (!((REG32(HMAC0_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET) >>
            HMAC_INTR_STATE_HMAC_DONE_BIT) &
           0x1)) {
  }
  REG32(HMAC0_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET) =
      1 << HMAC_INTR_STATE_HMAC_DONE_BIT;

  for (uint32_t i = 0; i < 8; i++) {
    *digest++ = REG32(HMAC0_BASE_ADDR + HMAC_DIGEST_0_REG_OFFSET +
                      i * sizeof(uintptr_t));
  }
}
