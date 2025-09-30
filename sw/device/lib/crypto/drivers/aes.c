// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/aes.h"

#include "hw/top/dt/aes.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top/aes_regs.h"  // Generated.

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'a', 'e')

static const dt_aes_t kAesDt = kDtAes;

static inline uint32_t aes_base(void) {
  return dt_aes_primary_reg_block(kAesDt);
}

enum {

  kAesKeyWordLen128 = 128 / (sizeof(uint32_t) * 8),
  kAesKeyWordLen192 = 192 / (sizeof(uint32_t) * 8),
  kAesKeyWordLen256 = 256 / (sizeof(uint32_t) * 8),
  kAesKeyWordLenMax = kAesKeyWordLen256,
};

/**
 * Spins until the AES hardware reports a specific status bit.
 */
static status_t spin_until(uint32_t bit) {
  while (true) {
    uint32_t reg = abs_mmio_read32(aes_base() + AES_STATUS_REG_OFFSET);
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
 * Consumes randomness; the caller must ensure the entropy complex is up.
 *
 * @param key AES key.
 * @return result, OK or error.
 */
static status_t aes_write_key(aes_key_t key) {
  if (key.sideload != kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(key.sideload, kHardenedBoolTrue);
    // Nothing to be done; key must be separately loaded from keymgr.
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_EQ(key.sideload, kHardenedBoolFalse);

  uint32_t share0 = aes_base() + AES_KEY_SHARE0_0_REG_OFFSET;
  uint32_t share1 = aes_base() + AES_KEY_SHARE1_0_REG_OFFSET;

  // Handle key shares in two separate hardened_memcpys to avoid dealing with
  // corresponding parts too close together, which could risk power
  // side-channel leakage in the ALU. Before writing the key shares, initialize
  // the registers with random data.
  hardened_memshred((uint32_t *)share0, kAesKeyWordLenMax);
  hardened_memcpy((uint32_t *)share0, key.key_shares[0], key.key_len);
  hardened_memshred((uint32_t *)share1, kAesKeyWordLenMax);
  hardened_memcpy((uint32_t *)share1, key.key_shares[1], key.key_len);

  // Check the integrity of the key written to the AES core.
  HARDENED_CHECK_EQ(aes_key_integrity_checksum_check(&key), kHardenedBoolTrue);

  return spin_until(AES_STATUS_IDLE_BIT);
}

/**
 * Compute the ctrl register value for the given parameters.
 *
 * @param key AES key.
 * @param encrypt True for encryption, false for decryption.
 * @return result, OK or error.
 */
static status_t compute_ctrl_reg(aes_key_t key, hardened_bool_t encrypt,
                                 uint32_t *ctrl_reg) {
  *ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;

  // Set the operation (encrypt or decrypt).
  hardened_bool_t operation_enc = launder32(0);
  switch (encrypt) {
    case kHardenedBoolTrue:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                 AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
      operation_enc = launder32(operation_enc) | kHardenedBoolTrue;
      break;
    case kHardenedBoolFalse:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                 AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC);
      operation_enc = launder32(operation_enc) | kHardenedBoolFalse;
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(operation_enc), encrypt);

  // Indicate whether the key will be sideloaded.
  hardened_bool_t which_sideload = launder32(0);
  switch (key.sideload) {
    case kHardenedBoolTrue:
      *ctrl_reg =
          bitfield_bit32_write(*ctrl_reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, true);
      which_sideload = launder32(which_sideload) | kHardenedBoolTrue;
      break;
    case kHardenedBoolFalse:
      *ctrl_reg = bitfield_bit32_write(*ctrl_reg,
                                       AES_CTRL_SHADOWED_SIDELOAD_BIT, false);
      which_sideload = launder32(which_sideload) | kHardenedBoolFalse;
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(which_sideload), key.sideload);

  // Translate the cipher mode to the hardware-encoding value and write the
  // control reg field.
  aes_cipher_mode_t mode_written = launder32(0);
  switch (launder32(key.mode)) {
    case kAesCipherModeEcb:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                 AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB);
      mode_written = launder32(mode_written) | kAesCipherModeEcb;
      break;
    case kAesCipherModeCbc:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                 AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC);
      mode_written = launder32(mode_written) | kAesCipherModeCbc;
      break;
    case kAesCipherModeCfb:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                 AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB);
      mode_written = launder32(mode_written) | kAesCipherModeCfb;
      break;
    case kAesCipherModeOfb:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                 AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB);
      mode_written = launder32(mode_written) | kAesCipherModeOfb;
      break;
    case kAesCipherModeCtr:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_MODE_FIELD,
                                 AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR);
      mode_written = launder32(mode_written) | kAesCipherModeCtr;
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(mode_written), key.mode);

  // Translate the key length to the hardware-encoding value and write the
  // control reg field.
  size_t key_len_written;
  switch (key.key_len) {
    case kAesKeyWordLen128:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                 AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128);
      key_len_written = launder32(kAesKeyWordLen128);
      break;
    case kAesKeyWordLen192:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                 AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192);
      key_len_written = launder32(kAesKeyWordLen192);
      break;
    case kAesKeyWordLen256:
      *ctrl_reg =
          bitfield_field32_write(*ctrl_reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                                 AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256);
      key_len_written = launder32(kAesKeyWordLen256);
      break;
    default:
      // Invalid value.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_len_written, key.key_len);

  // Never enable manual operation.
  *ctrl_reg = bitfield_bit32_write(
      *ctrl_reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, false);

  // Always set the PRNG reseed rate to once per 64 blocks.
  *ctrl_reg = bitfield_field32_write(
      *ctrl_reg, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD,
      AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64);
  return OTCRYPTO_OK;
}

status_t aes_verify_ctrl_reg(aes_key_t key, hardened_bool_t encrypt) {
  uint32_t ctrl_reg;

  HARDENED_TRY(compute_ctrl_reg(key, encrypt, &ctrl_reg));
  HARDENED_CHECK_EQ(abs_mmio_read32(aes_base() + AES_CTRL_SHADOWED_REG_OFFSET),
                    launder32(ctrl_reg));

  return OTCRYPTO_OK;
}

status_t aes_verify_ctrl_aux_reg(void) {
  // This has not been configured, so it is at its reset state.
  uint32_t ctrl_aux_reg = 0x1;

  HARDENED_CHECK_EQ(
      abs_mmio_read32(aes_base() + AES_CTRL_AUX_SHADOWED_REG_OFFSET),
      launder32(ctrl_aux_reg));

  return OTCRYPTO_OK;
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
  // Ensure the entropy complex is in an appropriate state. The AES block seeds
  // its PRNG from EDN for masking every time a new key is provided.
  HARDENED_TRY(entropy_complex_check());

  // Wait for the AES block to be idle.
  HARDENED_TRY(spin_until(AES_STATUS_IDLE_BIT));

  uint32_t ctrl_reg;

  HARDENED_TRY(compute_ctrl_reg(key, encrypt, &ctrl_reg));

  abs_mmio_write32_shadowed(aes_base() + AES_CTRL_SHADOWED_REG_OFFSET,
                            ctrl_reg);
  HARDENED_TRY(spin_until(AES_STATUS_IDLE_BIT));

  // Write the key (if it is not sideloaded).
  HARDENED_TRY(aes_write_key(key));

  // All modes except ECB need to set an IV.
  if (key.mode != kAesCipherModeEcb) {
    HARDENED_CHECK_NE(launder32(key.mode), kAesCipherModeEcb);
    uint32_t iv_offset = aes_base() + AES_IV_0_REG_OFFSET;
    for (size_t i = 0; i < ARRAYSIZE(iv->data); ++i) {
      abs_mmio_write32(iv_offset + i * sizeof(uint32_t), iv->data[i]);
    }
  }

  // Read back the AES configuration and compare to the expected configuration.
  HARDENED_CHECK_EQ(abs_mmio_read32(aes_base() + AES_CTRL_SHADOWED_REG_OFFSET),
                    launder32(ctrl_reg));

  // Check that AES is ready to receive input data.
  uint32_t status = abs_mmio_read32(aes_base() + AES_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(status, AES_STATUS_INPUT_READY_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }
  HARDENED_CHECK_EQ(launder32(bitfield_bit32_read(
                        abs_mmio_read32(aes_base() + AES_STATUS_REG_OFFSET),
                        AES_STATUS_INPUT_READY_BIT)),
                    true);

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
    uint32_t reg = abs_mmio_read32(aes_base() + AES_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, AES_STATUS_IDLE_BIT) &&
        !bitfield_bit32_read(reg, AES_STATUS_OUTPUT_VALID_BIT)) {
      return OTCRYPTO_RECOV_ERR;
    }

    HARDENED_TRY(spin_until(AES_STATUS_OUTPUT_VALID_BIT));

    uint32_t offset = aes_base() + AES_DATA_OUT_0_REG_OFFSET;
    size_t i;
    for (i = 0; launder32(i) < ARRAYSIZE(dest->data); ++i) {
      dest->data[i] = abs_mmio_read32(offset + i * sizeof(uint32_t));
    }
    // Check that the loop ran for the correct number of iterations.
    HARDENED_CHECK_EQ(i, ARRAYSIZE(dest->data));
  }

  if (src != NULL) {
    HARDENED_TRY(spin_until(AES_STATUS_INPUT_READY_BIT));

    uint32_t offset = aes_base() + AES_DATA_IN_0_REG_OFFSET;
    size_t i;
    for (i = 0; launder32(i) < ARRAYSIZE(src->data); ++i) {
      abs_mmio_write32(offset + i * sizeof(uint32_t), src->data[i]);
    }
    // Check that the loop ran for the correct number of iterations.
    HARDENED_CHECK_EQ(i, ARRAYSIZE(src->data));
  }

  return OTCRYPTO_OK;
}

status_t aes_end(aes_block_t *iv) {
  uint32_t ctrl_reg = AES_CTRL_SHADOWED_REG_RESVAL;
  ctrl_reg = bitfield_bit32_write(ctrl_reg,
                                  AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
  abs_mmio_write32_shadowed(aes_base() + AES_CTRL_SHADOWED_REG_OFFSET,
                            ctrl_reg);

  if (iv != NULL) {
    // Read back the current IV from the hardware.
    uint32_t iv_offset = aes_base() + AES_IV_0_REG_OFFSET;
    size_t i;
    for (i = 0; launder32(i) < ARRAYSIZE(iv->data); ++i) {
      iv->data[i] = abs_mmio_read32(iv_offset + i * sizeof(uint32_t));
    }
    // Check that the loop ran for the correct number of iterations.
    HARDENED_CHECK_EQ(i, ARRAYSIZE(iv->data));
  }

  uint32_t trigger_reg = 0;
  trigger_reg = bitfield_bit32_write(
      trigger_reg, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
  trigger_reg =
      bitfield_bit32_write(trigger_reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
  abs_mmio_write32(aes_base() + AES_TRIGGER_REG_OFFSET, trigger_reg);

  return spin_until(AES_STATUS_IDLE_BIT);
}

uint32_t aes_key_integrity_checksum(const aes_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->mode);
  crc32_add32(&ctx, key->sideload);
  crc32_add32(&ctx, key->key_len);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)key->key_shares[0], key->key_len);
  return crc32_finish(&ctx);
}

hardened_bool_t aes_key_integrity_checksum_check(const aes_key_t *key) {
  if (key->checksum == launder32(aes_key_integrity_checksum(key))) {
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
