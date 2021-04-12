// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/hmac.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hmac_regs.h"  // Generated.

rom_error_t hmac_sha256_init(const hmac_t *hmac) {
  if (hmac == NULL) {
    return kErrorHmacInvalidArgument;
  }

  // Clear the config, stopping the SHA engine.
  mmio_region_write32(hmac->base_addr, HMAC_CFG_REG_OFFSET, 0u);

  // Disable and clear interrupts
  mmio_region_write32(hmac->base_addr, HMAC_INTR_ENABLE_REG_OFFSET, 0u);
  mmio_region_write32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET, 0u);

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
  reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
  mmio_region_write32(hmac->base_addr, HMAC_CFG_REG_OFFSET, reg);

  reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_START_BIT, true);
  mmio_region_write32(hmac->base_addr, HMAC_CMD_REG_OFFSET, reg);

  return kErrorOk;
}

rom_error_t hmac_sha256_update(const hmac_t *hmac, const void *data,
                               size_t len) {
  if (hmac == NULL || data == NULL) {
    return kErrorHmacInvalidArgument;
  }
  const uint8_t *data_sent = (const uint8_t *)data;

  // Individual byte writes are needed if the buffer isn't word aligned.
  for (; len != 0 && (uintptr_t)data_sent & 3; --len) {
    mmio_region_write8(hmac->base_addr, HMAC_MSG_FIFO_REG_OFFSET, *data_sent++);
  }

  for (; len >= sizeof(uint32_t); len -= sizeof(uint32_t)) {
    // FIXME: read_32 does not work for unittests.
    uint32_t data_aligned = *(const uint32_t *)data_sent;
    mmio_region_write32(hmac->base_addr, HMAC_MSG_FIFO_REG_OFFSET,
                        data_aligned);
    data_sent += sizeof(uint32_t);
  }

  // Handle non-32bit aligned bytes at the end of the buffer.
  for (; len != 0; --len) {
    mmio_region_write8(hmac->base_addr, HMAC_MSG_FIFO_REG_OFFSET, *data_sent++);
  }
  return kErrorOk;
}

rom_error_t hmac_sha256_final(const hmac_t *hmac, hmac_digest_t *digest) {
  if (hmac == NULL || digest == NULL) {
    return kErrorHmacInvalidArgument;
  }

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_PROCESS_BIT, true);
  mmio_region_write32(hmac->base_addr, HMAC_CMD_REG_OFFSET, reg);

  do {
    reg = mmio_region_read32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, HMAC_INTR_STATE_HMAC_DONE_BIT));

  reg = bitfield_bit32_write(reg, HMAC_INTR_STATE_HMAC_DONE_BIT, false);
  mmio_region_write32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET, reg);

  mmio_region_memcpy_from_mmio32(hmac->base_addr, HMAC_DIGEST_0_REG_OFFSET,
                                 digest->digest,
                                 HMAC_PARAM_NUMWORDS * sizeof(uint32_t));
  return kErrorOk;
}
