// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hmac.h"

#include "common.h"
#include "hmac_regs.h"

#define HMAC0_BASE_ADDR 0x40120000
#define HMAC_FIFO_MAX 16
#define HMAC_FIFO_GROUP_SIZE HMAC_FIFO_MAX / 2

void hmac_init(hmac_cfg_t hmac_cfg) {
  REG32(HMAC_CFG(0)) = hmac_cfg.input_endian_swap << HMAC_CFG_ENDIAN_SWAP |
                       1 << hmac_cfg.mode |
                       hmac_cfg.digest_endian_swap << HMAC_CFG_DIGEST_SWAP;

  REG32(HMAC_MSG_LENGTH_LOWER(0)) = hmac_cfg.length_lower;
  REG32(HMAC_MSG_LENGTH_UPPER(0)) = hmac_cfg.length_upper;

  for (int i = 0; i < 8; i++) {
    REG32(HMAC_KEY0(0) + i * sizeof(uint32_t)) = hmac_cfg.keys[i];
  }

  REG32(HMAC_CMD(0)) = -1;
};

int hmac_fifo_full(void) {
  return (REG32(HMAC_STATUS(0)) >> HMAC_STATUS_FIFO_FULL) & 0x1;
}

static int hmac_fifo_depth(void) {
  return (REG32(HMAC_STATUS(0)) >> HMAC_STATUS_FIFO_DEPTH_OFFSET) &
         HMAC_STATUS_FIFO_DEPTH_MASK;
}

static int fifo_avail(void) { return HMAC_FIFO_MAX - hmac_fifo_depth(); }

void hmac_write(const void *data, size_t size_in_bytes) {
  const uint8_t *bp;
  const uint32_t *wp;
  uint32_t bytes_per_word = sizeof(uint32_t) / sizeof(uint8_t);
  uint32_t bytes_left_over = (size_in_bytes % bytes_per_word);
  size_t words_remaining = size_in_bytes / bytes_per_word;

  wp = (uint32_t *)data;

  // write in all words
  while (words_remaining > 0) {
    if (words_remaining > HMAC_FIFO_GROUP_SIZE) {
      // wait until FIFO is at least half drained
      while (fifo_avail() <= HMAC_FIFO_GROUP_SIZE) {
      }

      // write a whole group
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      words_remaining -= HMAC_FIFO_GROUP_SIZE;

    } else {
      REG32(HMAC_MSG_FIFO(0)) = *wp++;
      words_remaining--;
    };
  }

  // TODO: this is necessary because hmac only understands words right now, we
  // cannot do a byte write.  Once that is addressed, change following to
  // byte writes directly
  // Despite no byte support, it would have been okay to just read the entire
  // word and write it to hmac, since hmac knows exactly which bytes to ignore /
  // process. The problem however, is that the DV environment does not like
  // reading of unknown data. So imagine if we have one byte (0xab) left over,
  // in DV memory, this is represented as
  // XXXX_XXab.  Our environment assertions will fail when a full word read is
  // made to the X's, thus it is converted to byte reads below to avoid that
  // problem
  uint32_t padded_word = 0;
  uint8_t *last_word_ptr = (uint8_t *)&padded_word;
  bp = (uint8_t *)wp;

  while (bytes_left_over > 0) {
    *last_word_ptr++ = *bp++;
    bytes_left_over--;
  }

  // this word is ignored if no bytes are left over
  REG32(HMAC_MSG_FIFO(0)) = padded_word;
}

int hmac_done(uint32_t *digest) {
  // TODO need a timeout mechanism
  // wait for done to assert
  while (!((REG32(HMAC_INTR_STATE(0)) >> HMAC_INTR_STATE_HMAC_DONE) & 0x1)) {
  }

  for (uint32_t i = 0; i < 8; i++) {
    *digest++ = REG32(HMAC_DIGEST0(0) + i * sizeof(uintptr_t));
  }

  // eventually when we timeout, need to return an error code
  return 0;
}
