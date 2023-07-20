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
 * Sets up the CFG value for a given per-transaction configuration.
 *
 * This only sets the right values for the ENDIAN_SWAP / DIGEST_SWAP values,
 * using the values in `config`.
 *
 * The implementation here is careful to only update `*device_config` once it
 * has calculated the entire value for the register, rather than gradually
 * updating it early. The value of `*device_config` is only updated if the
 * function returns #kDifOk.
 *
 * @param[inout] device_config HMAC CFG register value to be updated;
 * @param config A per-transaction configuration.
 * @returns #kDifError if the config is invalid, #kDifOk if
 * `*device_config` was sucessfully updated.
 */
static dif_result_t dif_hmac_calculate_device_config_value(
    uint32_t *device_config, const dif_hmac_transaction_t config) {
  // Set the byte-order of the input message.
  bool swap_message_endianness;
  switch (config.message_endianness) {
    case kDifHmacEndiannessBig:
      swap_message_endianness = true;
      break;
    case kDifHmacEndiannessLittle:
      swap_message_endianness = false;
      break;
    default:
      return kDifError;
  }

  // Set the byte-order of the digest.
  bool swap_digest_endianness;
  switch (config.digest_endianness) {
    case kDifHmacEndiannessBig:
      swap_digest_endianness = true;
      break;
    case kDifHmacEndiannessLittle:
      swap_digest_endianness = false;
      break;
    default:
      return kDifError;
  }

  // `*device_config` must only be updated after the two switch statements,
  // because they can return #kDifError.
  *device_config = bitfield_bit32_write(
      *device_config, HMAC_CFG_ENDIAN_SWAP_BIT, swap_message_endianness);
  *device_config = bitfield_bit32_write(
      *device_config, HMAC_CFG_DIGEST_SWAP_BIT, swap_digest_endianness);

  return kDifOk;
}

dif_result_t dif_hmac_mode_hmac_start(const dif_hmac_t *hmac,
                                      const uint8_t *key,
                                      const dif_hmac_transaction_t config) {
  if (hmac == NULL || key == NULL) {
    return kDifBadArg;
  }

  // Read current CFG register value.
  uint32_t reg = mmio_region_read32(hmac->base_addr, HMAC_CFG_REG_OFFSET);

  // Set the byte-order of the input message and the digest.
  DIF_RETURN_IF_ERROR(dif_hmac_calculate_device_config_value(&reg, config));

  // Set the HMAC key.
  // The least significant word is at HMAC_KEY_7_REG_OFFSET.
  // From the HWIP spec: "Order of the secret key is: key[255:0] = {KEY0, KEY1,
  // KEY2, ... , KEY7};"
  for (size_t i = 0; i < HMAC_PARAM_NUM_WORDS; ++i) {
    const ptrdiff_t word_offset = (ptrdiff_t)(i * sizeof(uint32_t));
    mmio_region_write32(hmac->base_addr, HMAC_KEY_7_REG_OFFSET - word_offset,
                        read_32((char *)key + word_offset));
  }

  // Set HMAC to process in HMAC mode (not SHA256-only mode).
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, true);
  mmio_region_write32(hmac->base_addr, HMAC_CFG_REG_OFFSET, reg);

  // Begin HMAC operation.
  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_START_BIT);
  return kDifOk;
}

dif_result_t dif_hmac_mode_sha256_start(const dif_hmac_t *hmac,
                                        const dif_hmac_transaction_t config) {
  if (hmac == NULL) {
    return kDifBadArg;
  }

  // Read current CFG register value.
  uint32_t reg = mmio_region_read32(hmac->base_addr, HMAC_CFG_REG_OFFSET);

  // Set the byte-order of the input message and the digest.
  DIF_RETURN_IF_ERROR(dif_hmac_calculate_device_config_value(&reg, config));

  // Set HMAC to process in SHA256-only mode (without HMAC mode).
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);

  // Write new CFG register value.
  mmio_region_write32(hmac->base_addr, HMAC_CFG_REG_OFFSET, reg);

  // Begin SHA256-only operation.
  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_START_BIT);

  return kDifOk;
}

dif_result_t dif_hmac_fifo_push(const dif_hmac_t *hmac, const void *data,
                                size_t len, size_t *bytes_sent) {
  if (hmac == NULL || data == NULL) {
    return kDifBadArg;
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
    return kDifIpFifoFull;
  }

  return kDifOk;
}

dif_result_t dif_hmac_fifo_count_entries(const dif_hmac_t *hmac,
                                         uint32_t *num_entries) {
  if (hmac == NULL || num_entries == NULL) {
    return kDifBadArg;
  }

  *num_entries = get_fifo_entry_count(hmac);

  return kDifOk;
}

dif_result_t dif_hmac_get_message_length(const dif_hmac_t *hmac,
                                         uint64_t *msg_len) {
  if (hmac == NULL || msg_len == NULL) {
    return kDifBadArg;
  }

  uint64_t msg_lower =
      mmio_region_read32(hmac->base_addr, HMAC_MSG_LENGTH_LOWER_REG_OFFSET);
  uint64_t msg_upper =
      mmio_region_read32(hmac->base_addr, HMAC_MSG_LENGTH_UPPER_REG_OFFSET);

  *msg_len = (msg_upper << 32) | msg_lower;

  return kDifOk;
}

dif_result_t dif_hmac_process(const dif_hmac_t *hmac) {
  if (hmac == NULL) {
    return kDifBadArg;
  }

  mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_CMD_REG_OFFSET,
                                  HMAC_CMD_HASH_PROCESS_BIT);
  return kDifOk;
}

dif_result_t dif_hmac_finish(const dif_hmac_t *hmac,
                             dif_hmac_digest_t *digest) {
  if (hmac == NULL || digest == NULL) {
    return kDifBadArg;
  }

  // Check if hmac_done is asserted.
  bool done = mmio_region_get_bit32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET,
                                    HMAC_INTR_STATE_HMAC_DONE_BIT);

  // Check if fifo_empty is asserted.
  bool fifo_empty = mmio_region_get_bit32(
      hmac->base_addr, HMAC_STATUS_REG_OFFSET, HMAC_STATUS_FIFO_EMPTY_BIT);

  if (done) {
    // Clear hmac_done.
    mmio_region_nonatomic_set_bit32(hmac->base_addr, HMAC_INTR_STATE_REG_OFFSET,
                                    HMAC_INTR_STATE_HMAC_DONE_BIT);
  } else if (!fifo_empty) {
    return kDifUnavailable;
  }

  // Read the digest in reverse to preserve the numerical value.
  // The least significant word is at HMAC_DIGEST_7_REG_OFFSET.
  // From the HWIP spec: "Order of the digest is: digest[255:0] = {DIGEST0,
  // DIGEST1, DIGEST2, ... , DIGEST7};"
  for (size_t i = 0; i < ARRAYSIZE(digest->digest); ++i) {
    digest->digest[i] = mmio_region_read32(
        hmac->base_addr,
        HMAC_DIGEST_7_REG_OFFSET - (ptrdiff_t)(i * sizeof(uint32_t)));
  }

  // Disable HMAC and SHA256 until the next transaction, clearing the current
  // digest.
  uint32_t device_config =
      mmio_region_read32(hmac->base_addr, HMAC_CFG_REG_OFFSET);
  device_config =
      bitfield_bit32_write(device_config, HMAC_CFG_SHA_EN_BIT, false);
  device_config =
      bitfield_bit32_write(device_config, HMAC_CFG_HMAC_EN_BIT, false);
  mmio_region_write32(hmac->base_addr, HMAC_CFG_REG_OFFSET, device_config);

  return kDifOk;
}

dif_result_t dif_hmac_wipe_secret(const dif_hmac_t *hmac, uint32_t entropy) {
  if (hmac == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(hmac->base_addr, HMAC_WIPE_SECRET_REG_OFFSET, entropy);

  return kDifOk;
}
