// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

#include "kmac_regs.h"  // Generated.

enum {
  /**
   * The maximum amount of usable bits in the output state.
   *
   * This constant may be assumed to be a multiple of 32.
   *
   * The actual number of usable bits may be lower than the value defined
   * depending on the mode in use. The intent is that this constant is useful
   * for sizing fixed length buffers.
   *
   * Formula for the rate in bits is:
   *
   *   r = 1600 - c
   *
   * Where c is the capacity (the security level in bits multiplied by two).
   *
   * The lowest security level is 128 (e.g. SHAKE128).
   */
  kDifKmacMaximumBitRate = 1600 - (2 * 128),
};

dif_result_t dif_kmac_customization_string_init(
    const char *data, size_t len, dif_kmac_customization_string_t *out) {
  if ((data == NULL && len != 0) || out == NULL) {
    return kDifBadArg;
  }

  if (len > kDifKmacMaxCustomizationStringLen) {
    return kDifBadArg;
  }

  static_assert(kDifKmacMaxCustomizationStringLen <= UINT16_MAX / 8,
                "length requires more than 3 bytes to left encode");
  static_assert(ARRAYSIZE(out->buffer) >= kDifKmacMaxCustomizationStringLen + 3,
                "buffer is not large enough");

  // Left encode length in bits.
  uint16_t bits = ((uint16_t)len) * 8;
  char *buffer = out->buffer;
  if (bits <= UINT8_MAX) {
    out->length = len + 2;
    *buffer++ = 1;
    *buffer++ = (char)bits;
  } else {
    out->length = len + 3;
    *buffer++ = 2;
    // Most significant byte is first (i.e. big-endian).
    *buffer++ = (char)(bits >> 8);
    *buffer++ = (char)bits;
  }

  memcpy(buffer, data, len);

  return kDifOk;
}

dif_result_t dif_kmac_function_name_init(const char *data, size_t len,
                                         dif_kmac_function_name_t *out) {
  if ((data == NULL && len != 0) || out == NULL) {
    return kDifBadArg;
  }

  if (len > kDifKmacMaxFunctionNameLen) {
    return kDifBadArg;
  }

  static_assert(kDifKmacMaxFunctionNameLen <= UINT8_MAX / 8,
                "length requires more than 2 bytes to left encode");
  static_assert(ARRAYSIZE(out->buffer) >= kDifKmacMaxFunctionNameLen + 2,
                "buffer is not large enough");

  // Length of the data to be stored into buffer.
  out->length = len + 2;

  // Left encode length in bits.
  out->buffer[0] = 1;
  out->buffer[1] = (char)(len * 8);

  memcpy(&out->buffer[2], data, len);

  return kDifOk;
}

/**
 * Report whether the hardware is currently idle.
 *
 * If the hardware is not idle then the `CFG` register is locked.
 *
 * @param kmac Handle.
 * @returns Whether the hardware is currently idle or not.
 */
static bool is_state_idle(const dif_kmac_t *kmac) {
  uint32_t reg = mmio_region_read32(kmac->base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_IDLE_BIT);
}

/**
 * Report whether the hardware is currently in the absorb state and accepting
 * writes to the message FIFO.
 *
 * Note that writes to the message FIFO may still block if it is full.
 *
 * @param kmac Handle.
 * @returns Whether the hardware is currently absorbing or not.
 */
static bool is_state_absorb(const dif_kmac_t *kmac) {
  uint32_t reg = mmio_region_read32(kmac->base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_ABSORB_BIT);
}

/**
 * Report whether the hardware is currently in the squeeze state which means
 * that the output state is valid and may be read by software.
 *
 * @param kmac Handle.
 * @returns Whether the hardware is currently in the squeeze state or not.
 */
static bool is_state_squeeze(const dif_kmac_t *kmac) {
  uint32_t reg = mmio_region_read32(kmac->base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_SQUEEZE_BIT);
}

/**
 * Report whether the hardware has indicated a error.
 *
 * @param kmac Handle.
 * @returns True if an error occurred, False otherwise.
 */
static bool has_error_occurred(const dif_kmac_t *kmac) {
  uint32_t reg =
      mmio_region_read32(kmac->base_addr, KMAC_INTR_STATE_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_INTR_STATE_KMAC_ERR_BIT);
}

dif_result_t dif_kmac_poll_status(const dif_kmac_t *kmac, uint32_t flag) {
  while (true) {
    uint32_t reg = mmio_region_read32(kmac->base_addr, KMAC_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, flag)) {
      break;
    }
    if (has_error_occurred(kmac)) {
      return kDifError;
    }
  }
  return kDifOk;
}

dif_result_t dif_kmac_configure(dif_kmac_t *kmac, dif_kmac_config_t config) {
  if (kmac == NULL) {
    return kDifBadArg;
  }

  // Entropy mode.
  uint32_t entropy_mode_value;
  bool entropy_ready = false;
  switch (config.entropy_mode) {
    case kDifKmacEntropyModeIdle:
      entropy_mode_value = KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_IDLE_MODE;
      break;
    case kDifKmacEntropyModeEdn:
      entropy_mode_value = KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_EDN_MODE;
      entropy_ready = true;
      break;
    case kDifKmacEntropyModeSoftware:
      entropy_mode_value = KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_SW_MODE;
      entropy_ready = true;
      break;
    default:
      return kDifBadArg;
  }

  // Check that the hardware is in an idle state.
  if (!is_state_idle(kmac)) {
    return kDifLocked;
  }

  // Write entropy period register.
  uint32_t entropy_period_reg = 0;
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_WAIT_TIMER_FIELD,
      config.entropy_wait_timer);
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_PRESCALER_FIELD,
      config.entropy_prescaler);

  mmio_region_write32(kmac->base_addr, KMAC_ENTROPY_PERIOD_REG_OFFSET,
                      entropy_period_reg);

  // Write threshold register.
  uint32_t entropy_threshold_reg =
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_RESVAL;
  entropy_threshold_reg = bitfield_field32_write(
      entropy_threshold_reg,
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_THRESHOLD_FIELD,
      config.entropy_hash_threshold);

  mmio_region_write32_shadowed(
      kmac->base_addr, KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_OFFSET,
      entropy_threshold_reg);

  // Write configuration register.
  uint32_t cfg_reg = 0;
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT,
                                 config.message_big_endian);
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT,
                           config.output_big_endian);
  cfg_reg = bitfield_field32_write(
      cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_MODE_FIELD, entropy_mode_value);
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT,
                           config.entropy_fast_process);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT,
                                 config.sideload);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_READY_BIT,
                                 entropy_ready);

  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_MASK_BIT,
                                 config.msg_mask);

  mmio_region_write32_shadowed(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET,
                               cfg_reg);

  // Write entropy seed registers.
  for (int i = 0; i < kDifKmacEntropySeedWords; ++i) {
    mmio_region_write32(kmac->base_addr,
                        KMAC_ENTROPY_SEED_0_REG_OFFSET +
                            (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t),
                        config.entropy_seed[i]);
  }

  return kDifOk;
}

/**
 * Calculate the rate (r) in bits from the given security level.
 *
 * @param security_level Security level in bits.
 * @returns Rate in bits.
 */
static uint32_t calculate_rate_bits(uint32_t security_level) {
  // Formula for the rate in bits is:
  //
  //   r = 1600 - c
  //
  // Where c is the capacity (the security level in bits multiplied by two).
  return 1600 - 2 * security_level;
}

dif_result_t dif_kmac_mode_sha3_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_sha3_t mode) {
  if (kmac == NULL || operation_state == NULL) {
    return kDifBadArg;
  }

  // Set key strength and calculate rate (r) and digest length (d) in 32-bit
  // words.
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeSha3Len224:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(224) / 32;
      operation_state->d = 224 / 32;
      break;
    case kDifKmacModeSha3Len256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(256) / 32;
      operation_state->d = 256 / 32;
      break;
    case kDifKmacModeSha3Len384:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(384) / 32;
      operation_state->d = 384 / 32;
      break;
    case kDifKmacModeSha3Len512:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512;
      operation_state->offset = 0;
      operation_state->r = calculate_rate_bits(512) / 32;
      operation_state->d = 512 / 32;
      break;
    default:
      return kDifBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac)) {
    return kDifError;
  }

  operation_state->squeezing = false;
  operation_state->append_d = false;

  // Configure SHA-3 mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Poll until the status register is in the 'absorb' state.
  return dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_ABSORB_BIT);
}

dif_result_t dif_kmac_mode_shake_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_shake_t mode) {
  if (kmac == NULL || operation_state == NULL) {
    return kDifBadArg;
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeShakeLen128:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128;
      operation_state->r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeShakeLen256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      operation_state->r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac)) {
    return kDifError;
  }
  operation_state->squeezing = false;
  operation_state->append_d = false;
  operation_state->d = 0;  // Zero indicates variable digest length.
  operation_state->offset = 0;

  // Configure SHAKE mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  return dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_ABSORB_BIT);
}

dif_result_t dif_kmac_mode_cshake_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_cshake_t mode, const dif_kmac_function_name_t *n,
    const dif_kmac_customization_string_t *s) {
  if (kmac == NULL || operation_state == NULL) {
    return kDifBadArg;
  }

  // Use SHAKE if both N and S are empty strings.
  bool n_is_empty = n == NULL || (n->buffer[0] == 1 && n->buffer[1] == 0);
  bool s_is_empty = s == NULL || (s->buffer[0] == 1 && s->buffer[1] == 0);
  if (n_is_empty && s_is_empty) {
    switch (mode) {
      case kDifKmacModeCshakeLen128:
        return dif_kmac_mode_shake_start(kmac, operation_state,
                                         kDifKmacModeShakeLen128);
      case kDifKmacModeCshakeLen256:
        return dif_kmac_mode_shake_start(kmac, operation_state,
                                         kDifKmacModeShakeLen256);
      default:
        return kDifBadArg;
    }
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeCshakeLen128:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128;
      operation_state->r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeCshakeLen256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      operation_state->r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac)) {
    return kDifError;
  }
  operation_state->squeezing = false;
  operation_state->append_d = false;
  operation_state->d = 0;  // Zero indicates variable digest length.
  operation_state->offset = 0;

  // Configure cSHAKE mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Calculate PREFIX register values.
  uint32_t prefix_regs[11] = {0};
  uint8_t *prefix_data = (uint8_t *)prefix_regs;
  if (n == NULL || n->length < 3) {
    // Append left encoded empty string.
    prefix_data[0] = 1;
    prefix_data[1] = 0;
    prefix_data += 2;
  } else {
    memcpy(prefix_data, n->buffer, n->length);
    prefix_data += n->length;
  }
  if (s == NULL || s->length == 0) {
    // Append left encoded empty string.
    prefix_data[0] = 1;
    prefix_data[1] = 0;
  } else {
    memcpy(prefix_data, s->buffer, s->length);
  }

  // Write PREFIX register values.
  const mmio_region_t base = kmac->base_addr;
  mmio_region_write32(base, KMAC_PREFIX_0_REG_OFFSET, prefix_regs[0]);
  mmio_region_write32(base, KMAC_PREFIX_1_REG_OFFSET, prefix_regs[1]);
  mmio_region_write32(base, KMAC_PREFIX_2_REG_OFFSET, prefix_regs[2]);
  mmio_region_write32(base, KMAC_PREFIX_3_REG_OFFSET, prefix_regs[3]);
  mmio_region_write32(base, KMAC_PREFIX_4_REG_OFFSET, prefix_regs[4]);
  mmio_region_write32(base, KMAC_PREFIX_5_REG_OFFSET, prefix_regs[5]);
  mmio_region_write32(base, KMAC_PREFIX_6_REG_OFFSET, prefix_regs[6]);
  mmio_region_write32(base, KMAC_PREFIX_7_REG_OFFSET, prefix_regs[7]);
  mmio_region_write32(base, KMAC_PREFIX_8_REG_OFFSET, prefix_regs[8]);
  mmio_region_write32(base, KMAC_PREFIX_9_REG_OFFSET, prefix_regs[9]);
  mmio_region_write32(base, KMAC_PREFIX_10_REG_OFFSET, prefix_regs[10]);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  return dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_ABSORB_BIT);
}

dif_result_t dif_kmac_mode_kmac_start(
    const dif_kmac_t *kmac, dif_kmac_operation_state_t *operation_state,
    dif_kmac_mode_kmac_t mode, size_t l, const dif_kmac_key_t *k,
    const dif_kmac_customization_string_t *s) {
  if (kmac == NULL || operation_state == NULL || k == NULL ||
      l > kDifKmacMaxOutputLenWords) {
    return kDifBadArg;
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeKmacLen128:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128;
      operation_state->r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeKmacLen256:
      kstrength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
      operation_state->r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifBadArg;
  }
  operation_state->squeezing = false;
  operation_state->offset = 0;
  operation_state->d = l;
  operation_state->append_d = true;

  uint32_t key_len;
  switch (k->length) {
    case kDifKmacKeyLen128:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY128;
      break;
    case kDifKmacKeyLen192:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY192;
      break;
    case kDifKmacKeyLen256:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY256;
      break;
    case kDifKmacKeyLen384:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY384;
      break;
    case kDifKmacKeyLen512:
      key_len = KMAC_KEY_LEN_LEN_VALUE_KEY512;
      break;
    default:
      return kDifBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac)) {
    return kDifError;
  }
  // Set key length and shares.
  mmio_region_write32(kmac->base_addr, KMAC_KEY_LEN_REG_OFFSET, key_len);
  for (int i = 0; i < ARRAYSIZE(k->share0); ++i) {
    mmio_region_write32(kmac->base_addr,
                        KMAC_KEY_SHARE0_0_REG_OFFSET +
                            (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t),
                        k->share0[i]);
    mmio_region_write32(kmac->base_addr,
                        KMAC_KEY_SHARE1_0_REG_OFFSET +
                            (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t),
                        k->share1[i]);
  }

  // Configure cSHAKE mode with the given strength and enable KMAC mode.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, true);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);
  mmio_region_write32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET, cfg_reg);

  // Initialize prefix registers with function name ("KMAC") and empty
  // customization string. The empty customization string will be overwritten if
  // a non-empty string is provided.
  uint32_t prefix_regs[11] = {
      0x4D4B2001,  //  1  32  'K' 'M'
      0x00014341,  // 'A' 'C'  1   0
  };

  // Encoded customization string (s) must be at least 3 bytes long if it is not
  // the empty string.
  if (s != NULL && s->length >= 3) {
    // First two bytes overwrite the pre-encoded empty customization string.
    prefix_regs[1] &= 0xFFFF;
    prefix_regs[1] |= (uint32_t)((uint8_t)s->buffer[0]) << 16;
    prefix_regs[1] |= (uint32_t)((uint8_t)s->buffer[1]) << 24;
    memcpy(&prefix_regs[2], &s->buffer[2], s->length - 2);
  }

  // Write PREFIX register values.
  const mmio_region_t base = kmac->base_addr;
  mmio_region_write32(base, KMAC_PREFIX_0_REG_OFFSET, prefix_regs[0]);
  mmio_region_write32(base, KMAC_PREFIX_1_REG_OFFSET, prefix_regs[1]);
  mmio_region_write32(base, KMAC_PREFIX_2_REG_OFFSET, prefix_regs[2]);
  mmio_region_write32(base, KMAC_PREFIX_3_REG_OFFSET, prefix_regs[3]);
  mmio_region_write32(base, KMAC_PREFIX_4_REG_OFFSET, prefix_regs[4]);
  mmio_region_write32(base, KMAC_PREFIX_5_REG_OFFSET, prefix_regs[5]);
  mmio_region_write32(base, KMAC_PREFIX_6_REG_OFFSET, prefix_regs[6]);
  mmio_region_write32(base, KMAC_PREFIX_7_REG_OFFSET, prefix_regs[7]);
  mmio_region_write32(base, KMAC_PREFIX_8_REG_OFFSET, prefix_regs[8]);
  mmio_region_write32(base, KMAC_PREFIX_9_REG_OFFSET, prefix_regs[9]);
  mmio_region_write32(base, KMAC_PREFIX_10_REG_OFFSET, prefix_regs[10]);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  return dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_ABSORB_BIT);
}

static void msg_fifo_write(const dif_kmac_t *kmac, const unsigned char *data,
                           size_t len) {
  // Copy message using aligned word sized loads and stores where possible to
  // improve performance. Note: the parts of the message copied a byte at a time
  // will not be byte swapped in big-endian mode.
  for (; len != 0 && ((uintptr_t)data) % sizeof(uint32_t); --len) {
    mmio_region_write8(kmac->base_addr, KMAC_MSG_FIFO_REG_OFFSET, *data++);
  }
  for (; len >= sizeof(uint32_t); len -= sizeof(uint32_t)) {
    mmio_region_write32(kmac->base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                        read_32(data));
    data += sizeof(uint32_t);
  }
  for (; len != 0; --len) {
    mmio_region_write8(kmac->base_addr, KMAC_MSG_FIFO_REG_OFFSET, *data++);
  }
}

dif_result_t dif_kmac_absorb(const dif_kmac_t *kmac,
                             dif_kmac_operation_state_t *operation_state,
                             const void *msg, size_t len, size_t *processed) {
  // Set the number of bytes processed to 0.
  if (processed != NULL) {
    *processed = 0;
  }

  if (kmac == NULL || operation_state == NULL || (msg == NULL && len != 0)) {
    return kDifBadArg;
  }

  // Check that an operation has been started.
  if (operation_state->r == 0) {
    return kDifError;
  }

  // Poll until the status register is in the 'absorb' state.
  if (!is_state_absorb(kmac)) {
    return kDifError;
  }

  // Copy message using aligned word sized loads and stores where possible to
  // improve performance. Note: the parts of the message copied a byte at a time
  // will not be byte swapped in big-endian mode.
  const unsigned char *data = (const unsigned char *)msg;
  dif_kmac_status_t status;
  while (len > 0) {
    // Read the status register.
    DIF_RETURN_IF_ERROR(dif_kmac_get_status(kmac, &status));

    // Calculate the remaining space in the message FIFO based on the
    // `FIFO_DEPTH` status field.
    size_t free_entries = (KMAC_PARAM_NUM_ENTRIES_MSG_FIFO - status.fifo_depth);
    size_t max_len = free_entries * KMAC_PARAM_NUM_BYTES_MSG_FIFO_ENTRY;
    size_t write_len = (len < max_len) ? len : max_len;
    msg_fifo_write(kmac, data, write_len);
    data += write_len;
    len -= write_len;

    // If `processed` is non-null, do not continue after the first iteration;
    // return the number of bytes written and `kDifKmacIncomplete`.
    if (processed != NULL) {
      *processed = write_len;
      break;
    }
  }

  return kDifOk;
}

dif_result_t dif_kmac_squeeze(const dif_kmac_t *kmac,
                              dif_kmac_operation_state_t *operation_state,
                              uint32_t *out, size_t len, size_t *processed) {
  if (kmac == NULL || operation_state == NULL || (out == NULL && len != 0)) {
    return kDifBadArg;
  }

  // Set `processed` to 0 so we can return early without setting it again.
  if (processed != NULL) {
    *processed = 0;
  }

  const mmio_region_t base = kmac->base_addr;

  // Move into squeezing state (if not already in it).
  // Do this even if the length requested is 0 or too big.
  if (!operation_state->squeezing) {
    if (operation_state->append_d) {
      // The KMAC operation requires that the output length (d) in bits be right
      // encoded and appended to the end of the message.
      // Note: kDifKmacMaxOutputLenWords could be reduced to make this code
      // simpler. For example, a maximum of `(UINT16_MAX - 32) / 32` (just under
      // 8 KiB) would mean that d is guaranteed to be less than 0xFFFF.
      uint32_t d = operation_state->d * 32;
      int len = 1 + (d > 0xFF) + (d > 0xFFFF) + (d > 0xFFFFFF);
      int shift = (len - 1) * 8;
      while (shift >= 8) {
        mmio_region_write8(base, KMAC_MSG_FIFO_REG_OFFSET,
                           (uint8_t)(d >> shift));
        shift -= 8;
      }
      mmio_region_write8(base, KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)d);
      mmio_region_write8(base, KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)len);
    }
    operation_state->squeezing = true;

    // Issue squeeze command.
    uint32_t cmd_reg = bitfield_field32_write(0, KMAC_CMD_CMD_FIELD,
                                              KMAC_CMD_CMD_VALUE_PROCESS);
    mmio_region_write32(base, KMAC_CMD_REG_OFFSET, cmd_reg);
  }

  // If the operation has a fixed length output then the total number of bytes
  // requested must not exceed that length.
  if (operation_state->d != 0 &&
      len > (operation_state->d - operation_state->offset)) {
    return kDifError;
  }

  if (len == 0) {
    return kDifOk;
  }

  while (len > 0) {
    size_t n = len;
    size_t remaining = operation_state->r - operation_state->offset;
    if (operation_state->d != 0 && operation_state->d < operation_state->r) {
      remaining = operation_state->d - operation_state->offset;
    }
    if (n > remaining) {
      n = remaining;
    }
    if (n == 0) {
      // Reduce the digest length to reflect consumed output state.
      if (operation_state->d != 0) {
        if (operation_state->d <= operation_state->r) {
          return kDifError;
        }
        operation_state->d -= operation_state->r;
      }

      // Issue run command to generate more state.
      uint32_t cmd_reg =
          bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_RUN);
      mmio_region_write32(base, KMAC_CMD_REG_OFFSET, cmd_reg);
      operation_state->offset = 0;
      continue;
    }

    // Poll the status register until in the 'squeeze' state.
    DIF_RETURN_IF_ERROR(
        dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_SQUEEZE_BIT));

    ptrdiff_t offset =
        KMAC_STATE_REG_OFFSET +
        (ptrdiff_t)operation_state->offset * (ptrdiff_t)sizeof(uint32_t);
    for (size_t i = 0; i < n; ++i) {
      // Read both shares from state register and combine using XOR.
      uint32_t share0 = mmio_region_read32(base, offset);
      uint32_t share1 =
          mmio_region_read32(base, offset + kDifKmacStateShareOffset);
      *out++ = share0 ^ share1;
      offset += sizeof(uint32_t);
    }
    operation_state->offset += n;
    len -= n;
    if (processed != NULL) {
      *processed += n;
    }
  }
  return kDifOk;
}

dif_result_t dif_kmac_end(const dif_kmac_t *kmac,
                          dif_kmac_operation_state_t *operation_state) {
  if (kmac == NULL || operation_state == NULL) {
    return kDifBadArg;
  }

  // The hardware should (must?) complete squeeze operation before the DONE
  // command is issued.
  if (!operation_state->squeezing) {
    return kDifError;
  }
  while (true) {
    if (is_state_squeeze(kmac)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  // Issue done command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_DONE);
  mmio_region_write32(kmac->base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Reset operation state.
  operation_state->squeezing = false;
  operation_state->append_d = false;
  operation_state->offset = 0;
  operation_state->r = 0;
  operation_state->d = 0;

  return kDifOk;
}

dif_result_t dif_kmac_config_is_locked(const dif_kmac_t *kmac,
                                       bool *is_locked) {
  if (kmac == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(kmac->base_addr, KMAC_CFG_REGWEN_REG_OFFSET);
  *is_locked = !bitfield_bit32_read(reg, KMAC_CFG_REGWEN_EN_BIT);
  return kDifOk;
}

dif_result_t dif_kmac_get_status(const dif_kmac_t *kmac,
                                 dif_kmac_status_t *kmac_status) {
  if (kmac == NULL || kmac_status == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(kmac->base_addr, KMAC_STATUS_REG_OFFSET);

  kmac_status->sha3_state = bitfield_field32_read(
      reg,
      (bitfield_field32_t){.mask = 0x07, .index = KMAC_STATUS_SHA3_IDLE_BIT});

  kmac_status->fifo_depth =
      bitfield_field32_read(reg, KMAC_STATUS_FIFO_DEPTH_FIELD);

  kmac_status->fifo_state = bitfield_field32_read(
      reg,
      (bitfield_field32_t){.mask = 0x03, .index = KMAC_STATUS_FIFO_EMPTY_BIT});

  kmac_status->faults = bitfield_field32_read(
      reg, (bitfield_field32_t){.mask = 0x03,
                                .index = KMAC_STATUS_ALERT_FATAL_FAULT_BIT});

  return kDifOk;
}

dif_result_t dif_kmac_get_hash_counter(const dif_kmac_t *kmac,
                                       uint32_t *hash_ctr) {
  if (kmac == NULL || hash_ctr == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(kmac->base_addr,
                                    KMAC_ENTROPY_REFRESH_HASH_CNT_REG_OFFSET);

  *hash_ctr =
      bitfield_field32_read(reg, KMAC_ENTROPY_REFRESH_HASH_CNT_HASH_CNT_FIELD);

  return kDifOk;
}

dif_result_t dif_kmac_get_error(const dif_kmac_t *kmac,
                                dif_kmac_error_t *error) {
  if (kmac == NULL || error == NULL) {
    return kDifBadArg;
  }

  *error = mmio_region_read32(kmac->base_addr, KMAC_ERR_CODE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_kmac_reset(const dif_kmac_t *kmac,
                            dif_kmac_operation_state_t *operation_state) {
  if (kmac == NULL || operation_state == NULL) {
    return kDifBadArg;
  }
  operation_state->d = 0;
  operation_state->r = 0;
  operation_state->offset = 0;
  operation_state->squeezing = false;
  uint32_t reg =
      mmio_region_read32(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET);
  reg = bitfield_bit32_write(reg, KMAC_CFG_SHADOWED_ERR_PROCESSED_BIT, 1);

  mmio_region_write32_shadowed(kmac->base_addr, KMAC_CFG_SHADOWED_REG_OFFSET,
                               reg);
  return kDifOk;
}
