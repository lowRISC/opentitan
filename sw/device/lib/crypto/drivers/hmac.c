// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'h', 'm')

/**
 * Stop any current operation on the HMAC block.
 *
 * In addition to stopping any in-progress operation, this routine:
 * - clears secret internal values and keys using the WIPE_SECRET register.
 * - disables and clears interrupts.
 */
static void hmac_halt(void) {
  // Clear the config, which stops operation if the HMAC block was running.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, 0);

  // Wipe secrets (e.g. key).
  // TODO: this value is used directy by the HMAC hardware to overwrite the
  // key; replace it with a random number read from Ibex's RND.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_WIPE_SECRET_REG_OFFSET,
                   0xffffffff);

  // Disable and clear interrupts. INTR_STATE register is rw1c.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET,
                   0);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   UINT32_MAX);
}

/**
 * Initialize the HMAC block.
 *
 * If `enable_hmac` is `kHardenedBoolTrue`, starts the block in HMAC mode. If
 * it is `kHardenedBoolFalse`, starts in SHA256 mode.
 *
 * @param enable_hmac Whether to start HMAC mode.
 */
static void hmac_init(hardened_bool_t enable_hmac) {
  uint32_t cfg = 0;
  // Digest is little-endian by default.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_DIGEST_SWAP_BIT, false);
  // Message is little-endian by default.
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  if (launder32(enable_hmac) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(enable_hmac, kHardenedBoolTrue);
    cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, true);
  } else {
    HARDENED_CHECK_EQ(enable_hmac, kHardenedBoolFalse);
    cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, false);
  }
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, cfg);

  uint32_t cmd = bitfield_bit32_write(0, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, cmd);
}

void hmac_sha256_init(void) {
  // Stop any currently in-progress operation.
  hmac_halt();

  // Initialize in SHA256 mode.
  hmac_init(kHardenedBoolFalse);
}

void hmac_hmac_init(const hmac_key_t *key) {
  // Stop any currently in-progress operation.
  hmac_halt();

  // Write key registers.
  static_assert(ARRAYSIZE(key->key) == 8, "Unexpected HMAC key size.");
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_0_REG_OFFSET,
                   key->key[0]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_1_REG_OFFSET,
                   key->key[1]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_2_REG_OFFSET,
                   key->key[2]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_3_REG_OFFSET,
                   key->key[3]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_4_REG_OFFSET,
                   key->key[4]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_5_REG_OFFSET,
                   key->key[5]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_6_REG_OFFSET,
                   key->key[6]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_KEY_7_REG_OFFSET,
                   key->key[7]);

  // Initialize in HMAC mode.
  hmac_init(kHardenedBoolTrue);
}

void hmac_update(const uint8_t *data, size_t len) {
  // Individual byte writes are needed if the buffer isn't word aligned.
  for (; len != 0 && (uintptr_t)data & 3; --len) {
    abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                    *data++);
  }

  for (; len >= sizeof(uint32_t); len -= sizeof(uint32_t)) {
    uint32_t data_aligned = read_32(data);
    abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                     data_aligned);
    data += sizeof(uint32_t);
  }

  // Handle non-32bit aligned bytes at the end of the buffer.
  for (; len != 0; --len) {
    abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                    *data++);
  }
}

void hmac_final(hmac_digest_t *digest) {
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

  // Clean up and put the block back in an idle state.
  hmac_halt();
}
