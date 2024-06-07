// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/hmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void hmac_sha256_init_endian(bool big_endian_digest) {
  // Clear the config, stopping the SHA engine.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, 0u);

  // Disable and clear interrupts. INTR_STATE register is rw1c.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET,
                   0u);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   UINT32_MAX);

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, big_endian_digest);
  reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
  // configure to run SHA-2 256 with 256-bit key
  reg = bitfield_field32_write(reg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256);
  reg = bitfield_field32_write(reg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_256);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, reg);

  reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg);
}

void hmac_sha256_update(const void *data, size_t len) {
  const uint8_t *data_sent = (const uint8_t *)data;

  // Individual byte writes are needed if the buffer isn't word aligned.
  for (; len != 0 && (uintptr_t)data_sent & 3; --len) {
    abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                    *data_sent++);
  }

  for (; len >= sizeof(uint32_t); len -= sizeof(uint32_t)) {
    uint32_t data_aligned = read_32(data_sent);
    abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                     data_aligned);
    data_sent += sizeof(uint32_t);
  }

  // Handle non-32bit aligned bytes at the end of the buffer.
  for (; len != 0; --len) {
    abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                    *data_sent++);
  }
}

void hmac_sha256_update_words(const uint32_t *data, size_t len) {
  for (size_t i = 0; i < len; i++) {
    abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                     data[i]);
  }
}

void hmac_sha256_final_truncated(uint32_t *digest, size_t len) {
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_PROCESS_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg);

  do {
    reg = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR +
                          HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   reg);

  uint32_t result, incr;
  reg = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET);
  if (bitfield_bit32_read(reg, HMAC_CFG_DIGEST_SWAP_BIT)) {
    // Big-endian output.
    result = HMAC_DIGEST_0_REG_OFFSET;
    incr = sizeof(uint32_t);
  } else {
    // Little-endian output.
    // Note: we rely on 32-bit integer wraparound to cause the result register
    // index to count down from 7 to 0.
    result = HMAC_DIGEST_7_REG_OFFSET;
    incr = (uint32_t) - sizeof(uint32_t);
  }

  // Ensure len is at most the digest length; this function should never be
  // called with a `len` that is too big, but this helps ensure it at runtime
  // just in case.
  len = len <= kHmacDigestNumWords ? len : kHmacDigestNumWords;
  for (uint32_t i = 0; i < len; ++i, result += incr) {
    digest[i] = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + result);
  }
}

void hmac_sha256(const void *data, size_t len, hmac_digest_t *digest) {
  hmac_sha256_init();
  hmac_sha256_update(data, len);
  hmac_sha256_final(digest);
}

extern void hmac_sha256_init(void);
extern void hmac_sha256_final(hmac_digest_t *digest);
