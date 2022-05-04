// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/aes.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "aes_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Spins until the AES hardware reports a specific status bit.
 */
static aes_error_t spin_until(uint32_t bit) {
  uint32_t aes = TOP_EARLGREY_AES_BASE_ADDR;
  while (true) {
    uint32_t reg = abs_mmio_read32(aes + AES_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT) ||
        bitfield_bit32_read(reg, AES_STATUS_ALERT_FATAL_FAULT_BIT)) {
      return kAesInternalError;
    }
    if (bitfield_bit32_read(reg, bit)) {
      return kAesOk;
    }
  }
}

aes_error_t aes_begin(aes_params_t params) {
  aes_error_t err = spin_until(AES_STATUS_IDLE_BIT);
  if (err != kAesOk) {
    return err;
  }

  uint32_t aes = TOP_EARLGREY_AES_BASE_ADDR;

  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;
  ctrl_reg = bitfield_field32_write(
      ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
      params.encrypt ? AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC
                     : AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC);

  uint32_t mode_code;
  switch (params.mode) {
    case kAesCipherModeEcb:
      mode_code = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB;
      break;
    case kAesCipherModeCbc:
      mode_code = AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC;
      break;
    case kAesCipherModeCfb:
      mode_code = AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB;
      break;
    case kAesCipherModeOfb:
      mode_code = AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB;
      break;
    case kAesCipherModeCtr:
      mode_code = AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR;
      break;
  }
  ctrl_reg =
      bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD, mode_code);

  uint32_t len_code;
  switch (params.key_len) {
    case kAesKeyLen128:
      len_code = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128;
      break;
    case kAesKeyLen192:
      len_code = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192;
      break;
    case kAesKeyLen256:
      len_code = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256;
      break;
  }
  ctrl_reg = bitfield_field32_write(ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                    len_code);

  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, false);
  abs_mmio_write32_shadowed(aes + AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);
  err = spin_until(AES_STATUS_IDLE_BIT);
  if (err != kAesOk) {
    return err;
  }

  uint32_t share0 = aes + AES_KEY_SHARE0_0_REG_OFFSET;
  uint32_t share1 = aes + AES_KEY_SHARE1_0_REG_OFFSET;
  size_t key_words = params.key_len / (8 * sizeof(uint32_t));
  for (size_t i = 0; i < key_words; ++i) {
    abs_mmio_write32(share0 + i * sizeof(uint32_t), params.key[0][i]);
    abs_mmio_write32(share1 + i * sizeof(uint32_t), params.key[1][i]);
  }
  for (size_t i = key_words; i < 8; ++i) {
    // NOTE: all eight share registers must be written; in the case we don't
    // have enough key data, we fill it with zeroes.
    abs_mmio_write32(share0 + i * sizeof(uint32_t), 0);
    abs_mmio_write32(share1 + i * sizeof(uint32_t), 0);
  }
  err = spin_until(AES_STATUS_IDLE_BIT);
  if (err != kAesOk) {
    return err;
  }

  // ECB does not need to set an IV, so we're done early.
  if (params.mode == kAesCipherModeEcb) {
    return kAesOk;
  }

  uint32_t iv_offset = aes + AES_IV_0_REG_OFFSET;
  for (size_t i = 0; i < ARRAYSIZE(params.iv); ++i) {
    abs_mmio_write32(iv_offset + i * sizeof(uint32_t), params.iv[i]);
  }

  return kAesOk;
}

aes_error_t aes_update(aes_block_t *dest, const aes_block_t *src) {
  uint32_t aes = TOP_EARLGREY_AES_BASE_ADDR;

  if (src != NULL) {
    aes_error_t err = spin_until(AES_STATUS_INPUT_READY_BIT);
    if (err != kAesOk) {
      return err;
    }

    uint32_t offset = aes + AES_DATA_IN_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(src->data); ++i) {
      abs_mmio_write32(offset + i * sizeof(uint32_t), src->data[i]);
    }
  }

  if (dest != NULL) {
    aes_error_t err = spin_until(AES_STATUS_OUTPUT_VALID_BIT);
    if (err != kAesOk) {
      return err;
    }

    uint32_t offset = aes + AES_DATA_OUT_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(dest->data); ++i) {
      dest->data[i] = abs_mmio_read32(offset + i * sizeof(uint32_t));
    }
  }

  return kAesOk;
}

aes_error_t aes_end(void) {
  uint32_t aes = TOP_EARLGREY_AES_BASE_ADDR;

  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;
  ctrl_reg = bitfield_bit32_write(ctrl_reg,
                                  AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
  abs_mmio_write32_shadowed(aes + AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);

  uint32_t trigger_reg = 0;
  trigger_reg = bitfield_bit32_write(
      trigger_reg, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
  trigger_reg =
      bitfield_bit32_write(trigger_reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
  abs_mmio_write32(aes + AES_TRIGGER_REG_OFFSET, trigger_reg);

  return spin_until(AES_STATUS_IDLE_BIT);
}
