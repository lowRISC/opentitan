// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_hmac.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "hmac_regs.h"  // Generated.

/**
 * Read the status register from `hmac`.
 *
 * @param hmac The HMAC device to read the status register from.
 * @return The contents of hmac.STATUS.
 */
static uint32_t get_status(const dif_hmac_t *hmac) {
  return mmio_region_read32(hmac->base_addr, HMAC_STATUS_REG_OFFSET);
}

/**
 * Returns the number of entries in the FIFO of `hmac`. If the FIFO is empty,
 * this function will return 0, and if the FIFO is full, this funciton will
 * return `HMAC_FIFO_MAX`.
 *
 * @param hmac The HMAC device to check the FIFO size of.
 * @return The number of entries in the HMAC FIFO.
 */
static uint32_t get_fifo_entry_count(const dif_hmac_t *hmac) {
  return bitfield_field32_read(get_status(hmac), HMAC_STATUS_FIFO_DEPTH_FIELD);
}

/**
 * A helper function for calculating `HMAC_FIFO_MAX` - `get_fifo_entry_count()`.
 */
static uint32_t get_fifo_available_space(const dif_hmac_t *hmac) {
  return HMAC_MSG_FIFO_SIZE_WORDS - get_fifo_entry_count(hmac);
}

/**
 * Convert from a `dif_hmac_interrupt_t` to the appropriate bit index.
 * INTR_STATE, INTR_ENABLE, and INTR_TEST registers have the same bit offset.
 */
static bool irq_bit_offset_get(dif_hmac_interrupt_t irq_type,
                               uint8_t *offset_out) {
  ptrdiff_t offset;
  switch (irq_type) {
    case kDifHmacInterruptHmacDone:
      offset = HMAC_INTR_COMMON_HMAC_DONE_BIT;
      break;
    case kDifHmacInterruptFifoEmpty:
      offset = HMAC_INTR_COMMON_FIFO_EMPTY_BIT;
      break;
    case kDifHmacInterruptHmacErr:
      offset = HMAC_INTR_COMMON_HMAC_ERR_BIT;
      break;
    default:
      return false;
  }

  *offset_out = offset;

  return true;
}

dif_hmac_result_t dif_hmac_init(const dif_hmac_config_t *config,
                                dif_hmac_t *hmac) {
  // Basic checks on parameters. In `kDifHmacModeHmac` mode a key is required.
  if (config == NULL || hmac == NULL) {
    return kDifHmacBadArg;
  }

  hmac->base_addr = config->base_addr;

  // Clear the config, stopping the SHA engine.
  mmio_region_write32(config->base_addr, HMAC_CFG_REG_OFFSET, 0);

  // Clear INTER.
  mmio_region_write32(config->base_addr, HMAC_INTR_STATE_REG_OFFSET,
                      (1 << HMAC_INTR_STATE_HMAC_DONE_BIT) |
                          (1 << HMAC_INTR_STATE_FIFO_EMPTY_BIT) |
                          (1 << HMAC_INTR_STATE_HMAC_ERR_BIT));

  uint32_t device_config = 0;

  // Set the byte-order of the input message.
  switch (config->message_endianness) {
    case kDifHmacEndiannessBig:
      device_config |= (1 << HMAC_CFG_ENDIAN_SWAP_BIT);
      break;
    case kDifHmacEndiannessLittle:
      break;
    default:
      return kDifHmacError;
  }

  // Set the byte-order of the digest.
  switch (config->digest_endianness) {
    case kDifHmacEndiannessBig:
      device_config |= (1 << HMAC_CFG_DIGEST_SWAP_BIT);
      break;
    case kDifHmacEndiannessLittle:
      break;
    default:
      return kDifHmacError;
  }

  // Write the configuration.
  mmio_region_write32(config->base_addr, HMAC_CFG_REG_OFFSET, device_config);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_irq_state_get(const dif_hmac_t *hmac,
                                         dif_hmac_interrupt_t irq_type,
                                         dif_hmac_enable_t *state) {
  if (hmac == NULL || state == NULL) {
    return kDifHmacBadArg;
  }

  uint8_t offset;
  if (!irq_bit_offset_get(irq_type, &offset)) {
    return kDifHmacError;
  }

  // Get the interrupt state.
  bool enabled = mmio_region_get_bit32(hmac->base_addr,
                                       HMAC_INTR_STATE_REG_OFFSET, offset);
  *state = (enabled ? kDifHmacEnable : kDifHmacDisable);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_irq_state_clear(const dif_hmac_t *hmac,
                                           dif_hmac_interrupt_t irq_type) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  uint8_t offset;
  if (!irq_bit_offset_get(irq_type, &offset)) {
    return kDifHmacError;
  }

  // Clear the interrupt state.
  mmio_region_write_only_set_bit32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET,
                                   offset);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_irqs_disable(const dif_hmac_t *hmac,
                                        uint32_t *state) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  // Pass the interrupt state back to the caller.
  if (state != NULL) {
    *state = mmio_region_read32(hmac->base_addr, HMAC_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all interrupts.
  mmio_region_write32(hmac->base_addr, HMAC_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_irqs_restore(const dif_hmac_t *hmac,
                                        uint32_t state) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  // Restore interrupt state.
  mmio_region_write32(hmac->base_addr, HMAC_INTR_ENABLE_REG_OFFSET, state);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_irq_control(const dif_hmac_t *hmac,
                                       dif_hmac_interrupt_t irq_type,
                                       dif_hmac_enable_t enable) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  uint8_t offset;
  if (!irq_bit_offset_get(irq_type, &offset)) {
    return kDifHmacError;
  }

  // Enable/Disable interrupt.
  if (enable == kDifHmacEnable) {
    mmio_region_nonatomic_set_bit32(hmac->base_addr,
                                    HMAC_INTR_ENABLE_REG_OFFSET, offset);
  } else {
    mmio_region_nonatomic_clear_bit32(hmac->base_addr,
                                      HMAC_INTR_ENABLE_REG_OFFSET, offset);
  }

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_irq_force(const dif_hmac_t *hmac,
                                     dif_hmac_interrupt_t irq_type) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  uint8_t offset;
  if (!irq_bit_offset_get(irq_type, &offset)) {
    return kDifHmacError;
  }

  // Force the requested interrupt.
  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_INTR_TEST_REG_OFFSET,
                                  offset);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_mode_hmac_start(const dif_hmac_t *hmac,
                                           const uint8_t *key) {
  if (hmac == NULL || key == NULL) {
    return kDifHmacBadArg;
  }

  // Disable SHA256 while configuring and to clear the digest.
  mmio_region_nonatomic_clear_bit32(hmac->base_addr, HMAC_CFG_REG_OFFSET,
                                    HMAC_CFG_SHA_EN_BIT);

  // Set the HMAC key.
  // TODO Static assert register layout.
  mmio_region_memcpy_to_mmio32(hmac->base_addr, HMAC_KEY_0_REG_OFFSET, key,
                               HMAC_PARAM_NUMWORDS * sizeof(uint32_t));

  // Set HMAC to process in HMAC mode (not SHA256-only mode).
  mmio_region_nonatomic_set_mask32(
      hmac->base_addr, HMAC_CFG_REG_OFFSET,
      (1 << HMAC_CFG_SHA_EN_BIT) | (1 << HMAC_CFG_HMAC_EN_BIT), 0);

  // Begin HMAC operation.
  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_START_BIT);
  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_mode_sha256_start(const dif_hmac_t *hmac) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  // Disable SHA256 while configuring and to clear the digest.
  mmio_region_nonatomic_clear_bit32(hmac->base_addr, HMAC_CFG_REG_OFFSET,
                                    HMAC_CFG_SHA_EN_BIT);

  // Disable HMAC mode.
  mmio_region_nonatomic_clear_bit32(hmac->base_addr, HMAC_CFG_REG_OFFSET,
                                    HMAC_CFG_HMAC_EN_BIT);

  // Set HMAC to process in SHA256-only mode.
  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CFG_REG_OFFSET,
                                  HMAC_CFG_SHA_EN_BIT);

  // Begin SHA256-only operation.
  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_START_BIT);

  return kDifHmacOk;
}

dif_hmac_fifo_result_t dif_hmac_fifo_push(const dif_hmac_t *hmac,
                                          const void *data, size_t len,
                                          size_t *bytes_sent) {
  if (hmac == NULL || data == NULL) {
    return kDifHmacFifoBadArg;
  }

  const uint8_t *data_sent = (const uint8_t *)data;
  size_t bytes_remaining = len;

  while (bytes_remaining > 0 && get_fifo_available_space(hmac) > 0) {
    bool word_aligned = (uintptr_t)data_sent % sizeof(uint32_t) == 0;
    size_t bytes_written = 0;

    if (bytes_remaining < sizeof(uint32_t) || !word_aligned) {
      // Individual byte writes are needed if the buffer isn't aligned or there
      // are no more full words to write.
      mmio_region_write8(hmac->base_addr, HMAC_MSG_FIFO_REG_OFFSET, *data_sent);
      bytes_written = 1;
    } else {
      // `data_sent` is word-aligned and there are still words to write.
      uint32_t word = read_32(data_sent);
      mmio_region_write32(hmac->base_addr, HMAC_MSG_FIFO_REG_OFFSET, word);
      bytes_written = sizeof(uint32_t);
    }

    bytes_remaining -= bytes_written;
    data_sent += bytes_written;
  }

  if (bytes_sent != NULL) {
    *bytes_sent = len - bytes_remaining;
  }

  if (bytes_remaining > 0) {
    return kDifHmacFifoFull;
  }

  return kDifHmacFifoOk;
}

dif_hmac_result_t dif_hmac_fifo_count_entries(const dif_hmac_t *hmac,
                                              uint32_t *num_entries) {
  if (hmac == NULL || num_entries == NULL) {
    return kDifHmacBadArg;
  }

  *num_entries = get_fifo_entry_count(hmac);

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_get_message_length(const dif_hmac_t *hmac,
                                              uint64_t *msg_len) {
  if (hmac == NULL || msg_len == NULL) {
    return kDifHmacBadArg;
  }

  uint64_t msg_lower =
      mmio_region_read32(hmac->base_addr, HMAC_MSG_LENGTH_LOWER_REG_OFFSET);
  uint64_t msg_upper =
      mmio_region_read32(hmac->base_addr, HMAC_MSG_LENGTH_UPPER_REG_OFFSET);

  *msg_len = (msg_upper << 32) | msg_lower;

  return kDifHmacOk;
}

dif_hmac_result_t dif_hmac_process(const dif_hmac_t *hmac) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_PROCESS_BIT);
  return kDifHmacOk;
}

dif_hmac_digest_result_t dif_hmac_digest_read(const dif_hmac_t *hmac,
                                              dif_hmac_digest_t *digest) {
  if (hmac == NULL || digest == NULL) {
    return kDifHmacDigestBadArg;
  }

  // Check if hmac_done is asserted.
  bool done = mmio_region_get_bit32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET,
                                    HMAC_INTR_STATE_HMAC_DONE_BIT);

  if (done) {
    // Clear hmac_done.
    mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET,
                                    HMAC_INTR_STATE_HMAC_DONE_BIT);
  } else {
    return kDifHmacDigestProcessing;
  }

  // Read the digest.
  // TODO Static assert register layout.
  mmio_region_memcpy_from_mmio32(hmac->base_addr, HMAC_DIGEST_0_REG_OFFSET,
                                 digest->digest,
                                 HMAC_PARAM_NUMWORDS * sizeof(uint32_t));

  return kDifHmacDigestOk;
}

dif_hmac_result_t dif_hmac_wipe_secret(const dif_hmac_t *hmac,
                                       uint32_t entropy) {
  if (hmac == NULL) {
    return kDifHmacBadArg;
  }

  mmio_region_write32(hmac->base_addr, HMAC_WIPE_SECRET_REG_OFFSET, entropy);

  return kDifHmacOk;
}
