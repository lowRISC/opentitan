// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

// For each x (denoting security strength) in {128, 224, 256, 384, 512}
// keccak_rates = (1600 - 2x) in given order
static uint32_t keccak_rates[] = {168, 144, 136, 104, 72};

/**
 * Wait until given status bit is set.
 *
 * Loops until the `bit_position` of status register reaches the value
 * `bit_value`.
 * @params bit_position The bit position in the status register.
 * @oarams bit_value Whether it should wait for 0 or 1.
 */
static kmac_error_t wait_status_bit(uint32_t bit_position, uint32_t bit_value) {
  while (true) {
    uint32_t reg =
        abs_mmio_read32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, KMAC_STATUS_ALERT_FATAL_FAULT_BIT) ||
        bitfield_bit32_read(reg, KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT)) {
      return kKmacInternalError;
    }
    if (bitfield_bit32_read(reg, bit_position) == bit_value) {
      return kKmacOk;
    }
  }
}

OT_WARN_UNUSED_RESULT
kmac_error_t kmac_init(kmac_operation_t operation) {
  kmac_error_t err;
  uint32_t cfg_reg;
  uint32_t common_cfg_reg = KMAC_CFG_SHADOWED_REG_RESVAL;

  // This probably needs to be set once per device boot rather than setting it
  // at every KMAC invocation.
  common_cfg_reg = bitfield_field32_write(
      common_cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_MODE_FIELD,
      KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_EDN_MODE);

  err = wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1);
  if (err != kKmacOk) {
    return err;
  }

  cfg_reg = common_cfg_reg;
  switch (operation) {
    case kSHAKE128:
      cfg_reg =
          bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                 KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE);
      break;

    case kSHAKE256:
      cfg_reg =
          bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                 KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE);
      break;

    case kSHA3_224:
      cfg_reg =
          bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                 KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
      break;

    case kSHA3_256:
      cfg_reg =
          bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                 KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
      break;

    case kSHA3_384:
      cfg_reg =
          bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                 KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
      break;

    case kSHA3_512:
      cfg_reg =
          bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                 KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
      break;

    default:
      return kKmacNotImplemented;
  }
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  return kKmacOk;
}

OT_WARN_UNUSED_RESULT
kmac_error_t kmac_update(const uint8_t *data, size_t data_len, uint8_t *digest,
                         size_t digest_len) {
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  kmac_error_t err;

  // Assumption(1): `data_len` > 0 and `digest_len` > 0
  // Assumption(2): data % 4 = 0, i.e. the data ptr is 32-bit aligned

  err = wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1);
  // Issue the start command, so that messages written to MSG_FIFO are forwarded
  // to Keccak
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_START);
  abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CMD_REG_OFFSET, cmd_reg);

  // Begin by writing a word at a time
  uint32_t *word_ptr = (uint32_t *)data;
  size_t i = 0;
  for (; i < data_len / 4; i++) {
    err = wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0);
    if (err != kKmacOk) {
      return err;
    }
    abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_MSG_FIFO_REG_OFFSET,
                     *word_ptr++);
  }
  uint8_t *byte_ptr = (uint8_t *)word_ptr;

  // For the last few bytes, we need to write byte at a time
  // i = 4*(data_len/4)
  for (i = 4 * i; i < data_len; i++) {
    err = wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0);
    if (err != kKmacOk) {
      return err;
    }
    abs_mmio_write8(
        TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_MSG_FIFO_REG_OFFSET + (i % 4),
        *byte_ptr++);
  }

  // Issue the process command, so that squeezing phase can start
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_PROCESS);
  abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CMD_REG_OFFSET, cmd_reg);

  // Wait until squeezing is done
  err = wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1);
  if (err != kKmacOk) {
    return err;
  }

  uint32_t cfg_reg = abs_mmio_read32(TOP_EARLGREY_KMAC_BASE_ADDR +
                                     KMAC_CFG_SHADOWED_REG_OFFSET);
  uint32_t keccak_str =
      bitfield_field32_read(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD);
  uint32_t keccak_rate = keccak_rates[keccak_str];
  // Finally, we can read the two shares of digest and XOR them
  // Here the counter i denotes the number of bytes read from Keccak state
  for (i = 0; i < digest_len; i++) {
    // Do we require additional Keccak rounds?
    if ((i % keccak_rate) == 0 && i > 0) {
      // if we consumed all Keccak state and aren't done yet, run one more
      // Keccak round
      cmd_reg = KMAC_CMD_REG_RESVAL;
      cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                       KMAC_CMD_CMD_VALUE_RUN);
      abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CMD_REG_OFFSET,
                       cmd_reg);

      // Let Keccak core finish the extra squeezing round
      err = wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1);
      if (err != kKmacOk) {
        return err;
      }
    }
    digest[i] = abs_mmio_read8(TOP_EARLGREY_KMAC_BASE_ADDR +
                               KMAC_STATE_REG_OFFSET + (i % keccak_rate));
    digest[i] ^=
        abs_mmio_read8(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_STATE_REG_OFFSET +
                       KMAC_STATE_SIZE_BYTES / 2 + (i % keccak_rate));
  }

  // Release the KMAC core, so that it goes back to idle mode
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_DONE);
  abs_mmio_write32(TOP_EARLGREY_KMAC_BASE_ADDR + KMAC_CMD_REG_OFFSET, cmd_reg);
  if (err != kKmacOk) {
    return err;
  }

  return kKmacOk;
}
