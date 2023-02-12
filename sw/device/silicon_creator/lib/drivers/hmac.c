// Copyright lowRISC contributors.
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

void hmac_sha256_init(void) {
  // Clear the config, stopping the SHA engine.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, 0u);

  // Disable and clear interrupts. INTR_STATE register is rw1c.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET,
                   0u);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   UINT32_MAX);

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
  reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
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

void hmac_sha256_final(hmac_digest_t *digest) {
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_PROCESS_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg);

  do {
    reg = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR +
                          HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   reg);

  // Read the digest in reverse to preserve the numerical value.
  // The least significant word is at HMAC_DIGEST_7_REG_OFFSET.
  for (size_t i = 0; i < ARRAYSIZE(digest->digest); ++i) {
    digest->digest[i] =
        abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_7_REG_OFFSET -
                        (i * sizeof(uint32_t)));
  }
}
