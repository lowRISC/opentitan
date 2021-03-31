// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "kmac_regs.h"

/**
 * Report whether the hardware is currently idle.
 *
 * If the hardware is not idle then the `CFG` register is locked.
 *
 * @param params Hardware parameters.
 * @returns Whether the hardware is currently idle or not.
 */
static bool is_idle(dif_kmac_params_t params) {
  uint32_t reg = mmio_region_read32(params.base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_IDLE_BIT);
}

/**
 * Report whether the hardware is currently in the absorb state and accepting
 * writes to the message FIFO.
 *
 * Note that writes to the message FIFO may still block if it is full.
 *
 * @param params Hardware parameters.
 * @returns Whether the hardware is currently absorbing or not.
 */
static bool is_absorbing(dif_kmac_params_t params) {
  uint32_t reg = mmio_region_read32(params.base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_ABSORB_BIT);
}

/**
 * Wrapper around mmio_region_write32 that reads back the register after
 * it has been written to verify that it was written successfully.
 *
 * @param base_addr Base address.
 * @param offset Offset of target register.
 * @param value The value to write to the register.
 * @returns Whether the register was successfully set to `value`.
 */
static bool checked_mmio_region_write32(mmio_region_t base_addr,
                                        ptrdiff_t offset, uint32_t value) {
  mmio_region_write32(base_addr, offset, value);
  return mmio_region_read32(base_addr, offset) == value;
}

dif_kmac_result_t dif_kmac_init(dif_kmac_params_t params, dif_kmac_t *kmac) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  // If the hardware is busy then the current operation needs to be stopped
  // before any configuration can take place.
  // TODO: force the current operation to stop.
  if (!is_idle(params)) {
    return kDifKmacError;
  }
  *kmac = (dif_kmac_t){.params = params};

  return kDifKmacOk;
}

dif_kmac_configure_result_t dif_kmac_configure(dif_kmac_t *kmac,
                                               dif_kmac_config_t config) {
  if (kmac == NULL) {
    return kDifKmacConfigureBadArg;
  }

  // Entropy mode.
  uint32_t entropy_mode_value;
  switch (config.entropy_mode) {
    case kDifKmacEntropyModeIdle:
      entropy_mode_value = KMAC_CFG_ENTROPY_MODE_VALUE_IDLE_MODE;
      break;
    case kDifKmacEntropyModeEdn:
      entropy_mode_value = KMAC_CFG_ENTROPY_MODE_VALUE_EDN_MODE;
      break;
    case kDifKmacEntropyModeSoftware:
      entropy_mode_value = KMAC_CFG_ENTROPY_MODE_VALUE_SW_MODE;
      break;
    default:
      return kDifKmacConfigureBadArg;
  }

  // Entropy fast process bit.
  bool entropy_fast_process;
  switch (config.entropy_fast_process) {
    case kDifKmacToggleEnabled:
      entropy_fast_process = true;
      break;
    case kDifKmacToggleDisabled:
      entropy_fast_process = false;
      break;
    default:
      return kDifKmacConfigureBadArg;
  }

  // Message endianness bit.
  bool msg_big_endian;
  switch (config.message_endianness) {
    case kDifKmacEndiannessLittle:
      msg_big_endian = false;
      break;
    case kDifKmacEndiannessBig:
      msg_big_endian = true;
      break;
    default:
      return kDifKmacConfigureBadArg;
  }

  // State endianness bit.
  bool state_big_endian;
  switch (config.output_state_endianness) {
    case kDifKmacEndiannessLittle:
      state_big_endian = false;
      break;
    case kDifKmacEndiannessBig:
      state_big_endian = true;
      break;
    default:
      return kDifKmacConfigureBadArg;
  }

  // Check that the hardware is in an idle state.
  if (!is_idle(kmac->params)) {
    return kDifKmacConfigureError;
  }

  // Write configuration register.
  uint32_t cfg_reg = 0;
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_MSG_ENDIANNESS_BIT,
                                 msg_big_endian);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_STATE_ENDIANNESS_BIT,
                                 state_big_endian);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_ENTROPY_MODE_FIELD,
                                   entropy_mode_value);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_ENTROPY_FAST_PROCESS_BIT,
                                 entropy_fast_process);
  if (!checked_mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET,
                                   cfg_reg)) {
    // Write to configuration register failed.
    return kDifKmacConfigureError;
  }

  // Write entropy period register.
  uint32_t entropy_period_reg = 0;
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_ENTROPY_TIMER_FIELD,
      config.entropy_reseed_interval);
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_WAIT_TIMER_FIELD,
      config.entropy_wait_timer);
  if (!checked_mmio_region_write32(kmac->params.base_addr,
                                   KMAC_ENTROPY_PERIOD_REG_OFFSET,
                                   entropy_period_reg)) {
    // Write to entropy period register failed.
    return kDifKmacConfigureError;
  }

  // Write entropy seed registers.
  if (!checked_mmio_region_write32(kmac->params.base_addr,
                                   KMAC_ENTROPY_SEED_LOWER_REG_OFFSET,
                                   (uint32_t)(config.entropy_seed))) {
    // Write to lower entropy seed register failed.
    return kDifKmacConfigureError;
  }
  if (!checked_mmio_region_write32(kmac->params.base_addr,
                                   KMAC_ENTROPY_SEED_UPPER_REG_OFFSET,
                                   (uint32_t)(config.entropy_seed >> 32))) {
    // Write to upper entropy seed register failed.
    return kDifKmacConfigureError;
  }

  return kDifKmacConfigureOk;
}

dif_kmac_configure_result_t dif_kmac_mode_sha3_start(
    dif_kmac_t *kmac, dif_kmac_mode_sha3_t mode) {
  if (kmac == NULL) {
    return kDifKmacConfigureBadArg;
  }

  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeSha3Len224:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L224;
      kmac->offset = 0;
      kmac->r = 1152 / 8;
      kmac->d = 224 / 8;
      break;
    case kDifKmacModeSha3Len256:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L256;
      kmac->offset = 0;
      kmac->r = 1088 / 8;
      kmac->d = 256 / 8;
      break;
    case kDifKmacModeSha3Len384:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L384;
      kmac->offset = 0;
      kmac->r = 832 / 8;
      kmac->d = 384 / 8;
      break;
    case kDifKmacModeSha3Len512:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L512;
      kmac->offset = 0;
      kmac->r = 576 / 8;
      kmac->d = 512 / 8;
      break;
    default:
      return kDifKmacConfigureBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_idle(kmac->params)) {
    return kDifKmacConfigureError;
  }

  // Configure SHA-3 mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET);
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_KSTRENGTH_FIELD, kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_MODE_FIELD,
                                   KMAC_CFG_MODE_VALUE_SHA3);
  if (!checked_mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET,
                                   cfg_reg)) {
    // Write to configuration register failed.
    return kDifKmacConfigureError;
  }

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Poll until the status register is in the 'absorbing' state.
  // TODO: is this loop necessary?
  while (true) {
    if (is_absorbing(kmac->params)) {
      break;
    }
    // TODO: check for error?
  }

  return kDifKmacConfigureOk;
}

dif_kmac_absorb_result_t dif_kmac_absorb(dif_kmac_t *kmac, const void *msg,
                                         size_t len, size_t *processed) {
  if (kmac == NULL || (msg == NULL && len != 0)) {
    return kDifKmacAbsorbBadArg;
  }

  // Check that the status register is in the 'absorbing' state.
  if (!is_absorbing(kmac->params)) {
    return kDifKmacAbsorbError;
  }

  // TODO: implement non-blocking version using `processed`.
  // TODO: copy message using word-sized loads/stores (message endianness?).

  for (size_t i = 0; i < len; ++i) {
    mmio_region_write8(kmac->params.base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                       ((const uint8_t *)msg)[i]);
  }

  if (processed != NULL) {
    *processed = len;
  }
  return kDifKmacAbsorbOk;
}

dif_kmac_squeeze_result_t dif_kmac_squeeze(dif_kmac_t *kmac, void *out,
                                           size_t len, size_t *processed) {
  if (kmac == NULL || (out == NULL && len != 0)) {
    return kDifKmacSqueezeBadArg;
  }

  // TODO: implement non-blocking version using `processed`.

  // Set `processed` to 0 so we can return early without setting it again.
  if (processed != NULL) {
    *processed = 0;
  }

  // Move into squeezing state (if not already in it).
  // Do this even if the length requested is 0 or too big.
  if (!kmac->squeezing) {
    kmac->squeezing = true;

    // Issue squeeze command.
    uint32_t cmd_reg = bitfield_field32_write(0, KMAC_CMD_CMD_FIELD,
                                              KMAC_CMD_CMD_VALUE_PROCESS);
    mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);
  }

  // If the operation has a fixed length output then the total number of bytes
  // requested must not exceed that length.
  if (kmac->d != 0 && len > (kmac->d - kmac->offset)) {
    return kDifKmacSqueezeFixedLengthExceeded;
  }

  if (len == 0) {
    // TODO: XOF: request more state if needed to support async use case?
    return kDifKmacSqueezeOk;
  }

  // Poll the status register until in the 'squeeze' state.
  // TODO: poll only once if processed != NULL.
  while (true) {
    uint32_t status_reg =
        mmio_region_read32(kmac->params.base_addr, KMAC_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_SQUEEZE_BIT)) {
      break;
    }
  }

  // Read out the state shares.
  // TODO: figure out what big-endian digest should mean for sub-word reads.
  while (len > 0) {
    size_t n = len;
    size_t remaining = (kmac->d == 0 ? kmac->r : kmac->d) - kmac->offset;
    if (n > remaining) {
      n = remaining;
    }
    if (n == 0) {
      // TODO: XOF: request more state.
      return kDifKmacSqueezeError;
    }

    // Copy two shares of state out of state registers.
    // TODO: only copy the values we need.
    uint32_t state0[168];
    mmio_region_memcpy_from_mmio32(kmac->params.base_addr,
                                   KMAC_STATE_REG_OFFSET, state0,
                                   ARRAYSIZE(state0));
    uint32_t state1[168];
    mmio_region_memcpy_from_mmio32(kmac->params.base_addr,
                                   KMAC_STATE_REG_OFFSET + 0x100, state1,
                                   ARRAYSIZE(state1));

    // Combine the two shares of state using XOR.
    for (uint32_t i = 0; i < ARRAYSIZE(state0); ++i) {
      state0[i] ^= state1[i];
    }

    // Copy the combined state into the destination array.
    const uint8_t *src = (const uint8_t *)state0;
    memcpy(out, &src[kmac->offset], n);
    kmac->offset += n;
    len -= n;
    if (processed != NULL) {
      *processed += n;
    }
  }
  return kDifKmacSqueezeOk;
}

dif_kmac_result_t dif_kmac_end(dif_kmac_t *kmac) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  // The hardware should (must?) complete squeeze operation before the DONE
  // command is issued.
  if (!kmac->squeezing) {
    return kDifKmacError;
  }
  while (true) {
    uint32_t status_reg =
        mmio_region_read32(kmac->params.base_addr, KMAC_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_SQUEEZE_BIT)) {
      break;
    }
    // TODO: check error?
  }

  // Issue done command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_DONE);
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Reset state.
  kmac->squeezing = false;
  kmac->offset = 0;
  kmac->r = 0;
  kmac->d = 0;

  // Poll status register until in idle state.
  while (true) {
    if (is_idle(kmac->params)) {
      break;
    }
    // TODO: check error?
  }

  return kDifKmacOk;
}
