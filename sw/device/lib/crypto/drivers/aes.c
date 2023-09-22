// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/aes.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "aes_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'a', 'e')

enum {
  kBase = TOP_EARLGREY_AES_BASE_ADDR,

  kAesKeyWordLen128 = 128 / (sizeof(uint32_t) * 8),
  kAesKeyWordLen192 = 192 / (sizeof(uint32_t) * 8),
  kAesKeyWordLen256 = 256 / (sizeof(uint32_t) * 8),
};

/**
 * Spins until the AES hardware reports a specific status bit.
 */
static status_t spin_until(uint32_t bit) {
  while (true) {
    uint32_t reg = abs_mmio_read32(kBase + AES_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT) ||
        bitfield_bit32_read(reg, AES_STATUS_ALERT_FATAL_FAULT_BIT)) {
      return OTCRYPTO_RECOV_ERR;
    }
    if (bitfield_bit32_read(reg, bit)) {
      return OTCRYPTO_OK;
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
static status_t aes_write_key(aes_key_t key) {
  if (key.sideload != kHardenedBoolFalse) {
    // Nothing to be done; key must be separately loaded from keymgr.
    return OTCRYPTO_OK;
  }

  uint32_t share0 = kBase + AES_KEY_SHARE0_0_REG_OFFSET;
  uint32_t share1 = kBase + AES_KEY_SHARE1_0_REG_OFFSET;

  // Handle key shares in two separate loops to avoid dealing with
  // corresponding parts too close together, which could risk power
  // side-channel leakage in the ALU.
  // TODO: randomize iteration order.
  size_t i = 0;
  for (; i < key.key_len; ++i) {
    abs_mmio_write32(share0 + i * sizeof(uint32_t), key.key_shares[0][i]);
  }
  HARDENED_CHECK_EQ(i, key.key_len);
  for (i = 0; i < key.key_len; ++i) {
    abs_mmio_write32(share1 + i * sizeof(uint32_t), key.key_shares[1][i]);
  }
  HARDENED_CHECK_EQ(i, key.key_len);

  // NOTE: all eight share registers must be written; in the case we don't have
  // enough key data, we fill it with zeroes.
  for (size_t i = key.key_len; i < 8; ++i) {
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
static status_t aes_begin(aes_key_t key, const aes_block_t *iv,
                          hardened_bool_t encrypt) {
  HARDENED_TRY(spin_until(AES_STATUS_IDLE_BIT));

  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;

  // Set the operation (encrypt or decrypt).
  hardened_bool_t operation_written = kHardenedBoolFalse;
  switch (encrypt) {
    case kHardenedBoolTrue:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                 AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
      operation_written = launder32(kHardenedBoolTrue);
      break;
    case kHardenedBoolFalse:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                 AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC);
      operation_written = launder32(kHardenedBoolTrue);
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(operation_written, kHardenedBoolTrue);

  // Indicate whether the key will be sideloaded.
  hardened_bool_t sideload_written = kHardenedBoolFalse;
  switch (key.sideload) {
    case kHardenedBoolTrue:
      ctrl_reg =
          bitfield_bit32_write(ctrl_reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, true);
      sideload_written = launder32(kHardenedBoolTrue);
      break;
    case kHardenedBoolFalse:
      ctrl_reg =
          bitfield_bit32_write(ctrl_reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, false);
      sideload_written = launder32(kHardenedBoolTrue);
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(sideload_written, kHardenedBoolTrue);

  // Translate the cipher mode to the hardware-encoding value and write the
  // control reg field.
  aes_cipher_mode_t mode_written;
  switch (launder32(key.mode)) {
    case kAesCipherModeEcb:
      ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                        AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB);
      mode_written = launder32(kAesCipherModeEcb);
      break;
    case kAesCipherModeCbc:
      ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                        AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC);
      mode_written = launder32(kAesCipherModeCbc);
      break;
    case kAesCipherModeCfb:
      ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                        AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB);
      mode_written = launder32(kAesCipherModeCfb);
      break;
    case kAesCipherModeOfb:
      ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                        AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB);
      mode_written = launder32(kAesCipherModeOfb);
      break;
    case kAesCipherModeCtr:
      ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                        AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR);
      mode_written = launder32(kAesCipherModeCtr);
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(mode_written, key.mode);

  // Translate the key length to the hardware-encoding value and write the
  // control reg field.
  switch (key.key_len) {
    case kAesKeyWordLen128:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                 AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128);
      break;
    case kAesKeyWordLen192:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                 AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192);
      break;
    case kAesKeyWordLen256:
      ctrl_reg =
          bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                 AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256);
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }

  // Never enable manual operation.
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, false);

  // Always set the PRNG reseed rate to once per 64 blocks.
  ctrl_reg =
      bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD,
                             AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64);

  abs_mmio_write32_shadowed(kBase + AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);
  HARDENED_TRY(spin_until(AES_STATUS_IDLE_BIT));

  // Write the key (if it is not sideloaded).
  HARDENED_TRY(aes_write_key(key));

  // ECB does not need to set an IV, so we're done early.
  if (key.mode == launder32(kAesCipherModeEcb)) {
    HARDENED_CHECK_EQ(key.mode, kAesCipherModeEcb);
    return OTCRYPTO_OK;
  }

  uint32_t iv_offset = kBase + AES_IV_0_REG_OFFSET;
  for (size_t i = 0; i < ARRAYSIZE(iv->data); ++i) {
    abs_mmio_write32(iv_offset + i * sizeof(uint32_t), iv->data[i]);
  }

  return OTCRYPTO_OK;
}

status_t aes_encrypt_begin(const aes_key_t key, const aes_block_t *iv) {
  return aes_begin(key, iv, kHardenedBoolTrue);
}

status_t aes_decrypt_begin(const aes_key_t key, const aes_block_t *iv) {
  return aes_begin(key, iv, kHardenedBoolFalse);
}

status_t aes_update(aes_block_t *dest, const aes_block_t *src) {
  if (dest != NULL) {
    // Check that either the output is valid or AES is busy, to avoid spinning
    // forever if the user passes a non-null `dest` when there is no output
    // pending.
    uint32_t reg = abs_mmio_read32(kBase + AES_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, AES_STATUS_IDLE_BIT) &&
        !bitfield_bit32_read(reg, AES_STATUS_OUTPUT_VALID_BIT)) {
      return OTCRYPTO_RECOV_ERR;
    }

    HARDENED_TRY(spin_until(AES_STATUS_OUTPUT_VALID_BIT));

    uint32_t offset = kBase + AES_DATA_OUT_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(dest->data); ++i) {
      dest->data[i] = abs_mmio_read32(offset + i * sizeof(uint32_t));
    }
  }

  if (src != NULL) {
    HARDENED_TRY(spin_until(AES_STATUS_INPUT_READY_BIT));

    uint32_t offset = kBase + AES_DATA_IN_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(src->data); ++i) {
      abs_mmio_write32(offset + i * sizeof(uint32_t), src->data[i]);
    }
  }

  return OTCRYPTO_OK;
}

status_t aes_end(aes_block_t *iv) {
  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;
  ctrl_reg = bitfield_bit32_write(ctrl_reg,
                                  AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
  abs_mmio_write32_shadowed(kBase + AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);

  if (iv != NULL) {
    // Read back the current IV from the hardware.
    uint32_t iv_offset = kBase + AES_IV_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(iv->data); ++i) {
      iv->data[i] = abs_mmio_read32(iv_offset + i * sizeof(uint32_t));
    }
  }

  uint32_t trigger_reg = 0;
  trigger_reg = bitfield_bit32_write(
      trigger_reg, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
  trigger_reg =
      bitfield_bit32_write(trigger_reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
  abs_mmio_write32(kBase + AES_TRIGGER_REG_OFFSET, trigger_reg);

  return spin_until(AES_STATUS_IDLE_BIT);
}
