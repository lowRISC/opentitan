// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/aes.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

#include "aes_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Static assertions for enum values.
OT_ASSERT_ENUM_VALUE(kAesCipherModeEcb, AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCbc, AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCfb, AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB);
OT_ASSERT_ENUM_VALUE(kAesCipherModeOfb, AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCtr, AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR);

OT_ASSERT_ENUM_VALUE(kAesKeyLen128, AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128);
OT_ASSERT_ENUM_VALUE(kAesKeyLen192, AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192);
OT_ASSERT_ENUM_VALUE(kAesKeyLen256, AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256);

enum {
  kBase = TOP_EARLGREY_AES_BASE_ADDR,

  kAesKeyWordLen128 = 4,
  kAesKeyWordLen192 = 6,
  kAesKeyWordLen256 = 8,
};

/**
 * Spins until the AES hardware reports a specific status bit.
 */
static aes_error_t spin_until(uint32_t bit) {
  while (true) {
    uint32_t reg = abs_mmio_read32(kBase + AES_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT) ||
        bitfield_bit32_read(reg, AES_STATUS_ALERT_FATAL_FAULT_BIT)) {
      return kAesInternalError;
    }
    if (bitfield_bit32_read(reg, bit)) {
      return kAesOk;
    }
  }
}

/**
 * Write the key to the AES hardware block.
 *
 * If the key is sideloaded, this is a no-op.
 *
 * @param key AES key.
 * @return result, OK or error.
 */
static aes_error_t aes_write_key(aes_key_t key) {
  if (key.sideload != kHardenedBoolFalse) {
    // Nothing to be done; key must be separately loaded from keymgr.
    return kAesOk;
  }

  size_t key_words;
  switch (key.key_len) {
    case kAesKeyLen128:
      key_words = kAesKeyWordLen128;
      break;
    case kAesKeyLen192:
      key_words = kAesKeyWordLen192;
      break;
    case kAesKeyLen256:
      key_words = kAesKeyWordLen256;
      break;
    default:
      return kAesInternalError;
  }

  uint32_t share0 = kBase + AES_KEY_SHARE0_0_REG_OFFSET;
  uint32_t share1 = kBase + AES_KEY_SHARE1_0_REG_OFFSET;

  for (size_t i = 0; i < key_words; ++i) {
    abs_mmio_write32(share0 + i * sizeof(uint32_t), key.key_shares[0][i]);
    abs_mmio_write32(share1 + i * sizeof(uint32_t), key.key_shares[1][i]);
  }
  for (size_t i = key_words; i < 8; ++i) {
    // NOTE: all eight share registers must be written; in the case we don't
    // have enough key data, we fill it with zeroes.
    abs_mmio_write32(share0 + i * sizeof(uint32_t), 0);
    abs_mmio_write32(share1 + i * sizeof(uint32_t), 0);
  }
  return spin_until(AES_STATUS_IDLE_BIT);
}

/**
 * Configure the AES block and write the key and IV if applicable.
 *
 * @param key AES key.
 * @param iv IV to use (ignored if the mode does not require an IV).
 * @param encrypt True for encryption, false for decryption.
 * @return result, OK or error.
 */
static aes_error_t aes_begin(aes_key_t key, const aes_block_t *iv,
                             hardened_bool_t encrypt) {
  aes_error_t err = spin_until(AES_STATUS_IDLE_BIT);
  if (err != kAesOk) {
    return err;
  }

  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;

  // Set the operation (encrypt or decrypt).
  hardened_bool_t operation_written = kHardenedBoolFalse;
  switch (encrypt) {
    case kHardenedBoolTrue:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                 AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
      operation_written = kHardenedBoolTrue;
      break;
    case kHardenedBoolFalse:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                 AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC);
      operation_written = kHardenedBoolTrue;
      break;
    default:
      // Invalid value.
      return kAesInternalError;
  }
  HARDENED_CHECK_EQ(operation_written, kHardenedBoolTrue);

  // Indicate whether the key will be sideloaded.
  hardened_bool_t sideload_written = kHardenedBoolFalse;
  switch (key.sideload) {
    case kHardenedBoolTrue:
      ctrl_reg =
          bitfield_bit32_write(ctrl_reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, true);
      sideload_written = kHardenedBoolTrue;
      break;
    case kHardenedBoolFalse:
      ctrl_reg =
          bitfield_bit32_write(ctrl_reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, false);
      sideload_written = kHardenedBoolTrue;
      break;
    default:
      // Invalid value.
      return kAesInternalError;
  }
  HARDENED_CHECK_EQ(sideload_written, kHardenedBoolTrue);

  // Set the mode and the key length.
  ctrl_reg =
      bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD, key.mode);
  ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                    key.key_len);

  // Never enable manual operation.
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, false);

  // Always set the PRNG reseed rate to once per 64 blocks.
  ctrl_reg =
      bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD,
                             AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64);

  abs_mmio_write32_shadowed(kBase + AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);
  err = spin_until(AES_STATUS_IDLE_BIT);
  if (err != kAesOk) {
    return err;
  }

  // Write the key (if it is not sideloaded).
  err = aes_write_key(key);
  if (err != kAesOk) {
    return err;
  }

  // ECB does not need to set an IV, so we're done early.
  if (key.mode == kAesCipherModeEcb) {
    return kAesOk;
  }

  uint32_t iv_offset = kBase + AES_IV_0_REG_OFFSET;
  for (size_t i = 0; i < ARRAYSIZE(iv->data); ++i) {
    abs_mmio_write32(iv_offset + i * sizeof(uint32_t), iv->data[i]);
  }

  return kAesOk;
}

aes_error_t aes_encrypt_begin(const aes_key_t key, const aes_block_t *iv) {
  return aes_begin(key, iv, kHardenedBoolTrue);
}

aes_error_t aes_decrypt_begin(const aes_key_t key, const aes_block_t *iv) {
  return aes_begin(key, iv, kHardenedBoolFalse);
}

aes_error_t aes_update(aes_block_t *dest, const aes_block_t *src) {
  if (src != NULL) {
    aes_error_t err = spin_until(AES_STATUS_INPUT_READY_BIT);
    if (err != kAesOk) {
      return err;
    }

    uint32_t offset = kBase + AES_DATA_IN_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(src->data); ++i) {
      abs_mmio_write32(offset + i * sizeof(uint32_t), src->data[i]);
    }
  }

  if (dest != NULL) {
    aes_error_t err = spin_until(AES_STATUS_OUTPUT_VALID_BIT);
    if (err != kAesOk) {
      return err;
    }

    uint32_t offset = kBase + AES_DATA_OUT_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(dest->data); ++i) {
      dest->data[i] = abs_mmio_read32(offset + i * sizeof(uint32_t));
    }
  }

  return kAesOk;
}

aes_error_t aes_end(void) {
  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;
  ctrl_reg = bitfield_bit32_write(ctrl_reg,
                                  AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
  abs_mmio_write32_shadowed(kBase + AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);

  uint32_t trigger_reg = 0;
  trigger_reg = bitfield_bit32_write(
      trigger_reg, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
  trigger_reg =
      bitfield_bit32_write(trigger_reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
  abs_mmio_write32(kBase + AES_TRIGGER_REG_OFFSET, trigger_reg);

  return spin_until(AES_STATUS_IDLE_BIT);
}
