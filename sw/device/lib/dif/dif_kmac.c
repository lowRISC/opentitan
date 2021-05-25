// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "kmac_regs.h"

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

  /**
   * The offset of the second share within the output state register.
   */
  kDifKmacStateShareOffset = 0x100,
};

dif_kmac_result_t dif_kmac_customization_string_init(
    const char *data, size_t len, dif_kmac_customization_string_t *out) {
  if ((data == NULL && len != 0) || out == NULL) {
    return kDifKmacBadArg;
  }

  if (len > kDifKmacMaxCustomizationStringLen) {
    return kDifKmacBadArg;
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

  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_function_name_init(const char *data, size_t len,
                                              dif_kmac_function_name_t *out) {
  if ((data == NULL && len != 0) || out == NULL) {
    return kDifKmacBadArg;
  }

  if (len > kDifKmacMaxFunctionNameLen) {
    return kDifKmacBadArg;
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

  return kDifKmacOk;
}

/**
 * Report whether the hardware is currently idle.
 *
 * If the hardware is not idle then the `CFG` register is locked.
 *
 * @param params Hardware parameters.
 * @returns Whether the hardware is currently idle or not.
 */
static bool is_state_idle(dif_kmac_params_t params) {
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
static bool is_state_absorb(dif_kmac_params_t params) {
  uint32_t reg = mmio_region_read32(params.base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_ABSORB_BIT);
}

/**
 * Report whether the hardware is currently in the squeeze state which means
 * that the output state is valid and may be read by software.
 *
 * @param params Hardware parameters.
 * @returns Whether the hardware is currently in the squeeze state or not.
 */
static bool is_state_squeeze(dif_kmac_params_t params) {
  uint32_t reg = mmio_region_read32(params.base_addr, KMAC_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, KMAC_STATUS_SHA3_SQUEEZE_BIT);
}

dif_kmac_result_t dif_kmac_init(dif_kmac_params_t params, dif_kmac_t *kmac) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  *kmac = (dif_kmac_t){.params = params};
  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_configure(dif_kmac_t *kmac,
                                     dif_kmac_config_t config) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  // Entropy mode.
  uint32_t entropy_mode_value;
  bool entropy_ready = false;
  switch (config.entropy_mode) {
    case kDifKmacEntropyModeIdle:
      entropy_mode_value = KMAC_CFG_ENTROPY_MODE_VALUE_IDLE_MODE;
      break;
    case kDifKmacEntropyModeEdn:
      entropy_mode_value = KMAC_CFG_ENTROPY_MODE_VALUE_EDN_MODE;
      entropy_ready = true;
      break;
    case kDifKmacEntropyModeSoftware:
      entropy_mode_value = KMAC_CFG_ENTROPY_MODE_VALUE_SW_MODE;
      break;
    default:
      return kDifKmacBadArg;
  }

  // Check that the hardware is in an idle state.
  if (!is_state_idle(kmac->params)) {
    return kDifKmacLocked;
  }

  // Write configuration register.
  uint32_t cfg_reg = 0;
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_MSG_ENDIANNESS_BIT,
                                 config.message_big_endian);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_STATE_ENDIANNESS_BIT,
                                 config.output_big_endian);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_ENTROPY_MODE_FIELD,
                                   entropy_mode_value);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_ENTROPY_FAST_PROCESS_BIT,
                                 config.entropy_fast_process);
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_ENTROPY_READY_BIT, entropy_ready);
  mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET, cfg_reg);

  // Write entropy period register.
  uint32_t entropy_period_reg = 0;
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_ENTROPY_TIMER_FIELD,
      config.entropy_reseed_interval);
  entropy_period_reg = bitfield_field32_write(
      entropy_period_reg, KMAC_ENTROPY_PERIOD_WAIT_TIMER_FIELD,
      config.entropy_wait_timer);
  mmio_region_write32(kmac->params.base_addr, KMAC_ENTROPY_PERIOD_REG_OFFSET,
                      entropy_period_reg);

  // Write entropy seed registers.
  mmio_region_write32(kmac->params.base_addr,
                      KMAC_ENTROPY_SEED_LOWER_REG_OFFSET,
                      (uint32_t)config.entropy_seed);
  mmio_region_write32(kmac->params.base_addr,
                      KMAC_ENTROPY_SEED_UPPER_REG_OFFSET,
                      (uint32_t)(config.entropy_seed >> 32));

  return kDifKmacOk;
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

dif_kmac_result_t dif_kmac_mode_sha3_start(dif_kmac_t *kmac,
                                           dif_kmac_mode_sha3_t mode) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  // Set key strength and calculate rate (r) and digest length (d) in 32-bit
  // words.
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeSha3Len224:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L224;
      kmac->offset = 0;
      kmac->r = calculate_rate_bits(224) / 32;
      kmac->d = 224 / 32;
      break;
    case kDifKmacModeSha3Len256:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L256;
      kmac->offset = 0;
      kmac->r = calculate_rate_bits(256) / 32;
      kmac->d = 256 / 32;
      break;
    case kDifKmacModeSha3Len384:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L384;
      kmac->offset = 0;
      kmac->r = calculate_rate_bits(384) / 32;
      kmac->d = 384 / 32;
      break;
    case kDifKmacModeSha3Len512:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L512;
      kmac->offset = 0;
      kmac->r = calculate_rate_bits(512) / 32;
      kmac->d = 512 / 32;
      break;
    default:
      return kDifKmacBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac->params)) {
    return kDifKmacError;
  }

  // Configure SHA-3 mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET);
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_KSTRENGTH_FIELD, kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_MODE_FIELD,
                                   KMAC_CFG_MODE_VALUE_SHA3);
  mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET, cfg_reg);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Poll until the status register is in the 'absorb' state.
  while (true) {
    if (is_state_absorb(kmac->params)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_mode_shake_start(dif_kmac_t *kmac,
                                            dif_kmac_mode_shake_t mode) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeShakeLen128:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L128;
      kmac->r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeShakeLen256:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L256;
      kmac->r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifKmacBadArg;
  }
  kmac->d = 0;  // Zero indicates variable digest length.
  kmac->offset = 0;

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac->params)) {
    return kDifKmacError;
  }

  // Configure SHAKE mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET);
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_KSTRENGTH_FIELD, kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_MODE_FIELD,
                                   KMAC_CFG_MODE_VALUE_SHAKE);
  mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET, cfg_reg);

  // Issue start command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_START);
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Poll until the status register is in the 'absorb' state.
  while (true) {
    if (is_state_absorb(kmac->params)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_mode_cshake_start(
    dif_kmac_t *kmac, dif_kmac_mode_cshake_t mode,
    const dif_kmac_function_name_t *n,
    const dif_kmac_customization_string_t *s) {
  if (kmac == NULL) {
    return kDifKmacBadArg;
  }

  // Use SHAKE if both N and S are empty strings.
  bool n_is_empty = n == NULL || (n->buffer[0] == 1 && n->buffer[1] == 0);
  bool s_is_empty = s == NULL || (s->buffer[0] == 1 && s->buffer[1] == 0);
  if (n_is_empty && s_is_empty) {
    switch (mode) {
      case kDifKmacModeCshakeLen128:
        return dif_kmac_mode_shake_start(kmac, kDifKmacModeShakeLen128);
      case kDifKmacModeCshakeLen256:
        return dif_kmac_mode_shake_start(kmac, kDifKmacModeShakeLen256);
      default:
        return kDifKmacBadArg;
    }
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeCshakeLen128:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L128;
      kmac->r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeCshakeLen256:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L256;
      kmac->r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifKmacBadArg;
  }
  kmac->d = 0;  // Zero indicates variable digest length.
  kmac->offset = 0;

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac->params)) {
    return kDifKmacError;
  }

  // Configure cSHAKE mode with the given strength.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET);
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_KSTRENGTH_FIELD, kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_MODE_FIELD,
                                   KMAC_CFG_MODE_VALUE_CSHAKE);
  mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET, cfg_reg);

  // Calculate PREFIX register values.
  uint32_t prefix_regs[11] = {0};
  uint8_t *prefix_data = (void *)prefix_regs;
  if (n == NULL) {
    // Append left encoded empty string.
    prefix_data[0] = 1;
    prefix_data[1] = 0;
    prefix_data += 2;
  } else {
    memcpy(prefix_data, n->buffer, n->length);
    prefix_data += n->length;
  }
  if (s == NULL) {
    // Append left encoded empty string.
    prefix_data[0] = 1;
    prefix_data[1] = 0;
  } else {
    memcpy(prefix_data, s->buffer, s->length);
  }

  // Write PREFIX register values.
  const mmio_region_t base = kmac->params.base_addr;
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
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Poll until the status register is in the 'absorb' state.
  while (true) {
    if (is_state_absorb(kmac->params)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_mode_kmac_start(
    dif_kmac_t *kmac, dif_kmac_mode_kmac_t mode, size_t l,
    const dif_kmac_key_t *k, const dif_kmac_customization_string_t *s) {
  if (kmac == NULL || k == NULL || l > kDifKmacMaxOutputLenWords) {
    return kDifKmacBadArg;
  }

  // Set key strength and calculate rate (r).
  uint32_t kstrength;
  switch (mode) {
    case kDifKmacModeCshakeLen128:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L128;
      kmac->r = calculate_rate_bits(128) / 32;
      break;
    case kDifKmacModeCshakeLen256:
      kstrength = KMAC_CFG_KSTRENGTH_VALUE_L256;
      kmac->r = calculate_rate_bits(256) / 32;
      break;
    default:
      return kDifKmacBadArg;
  }
  kmac->offset = 0;
  kmac->d = l;
  kmac->append_d = true;

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
      return kDifKmacBadArg;
  }

  // Hardware must be idle to start an operation.
  if (!is_state_idle(kmac->params)) {
    return kDifKmacError;
  }

  // Set key length and shares.
  mmio_region_write32(kmac->params.base_addr, KMAC_KEY_LEN_REG_OFFSET, key_len);
  for (int i = 0; i < ARRAYSIZE(k->share0); ++i) {
    mmio_region_write32(kmac->params.base_addr,
                        KMAC_KEY_SHARE0_0_REG_OFFSET + i * sizeof(uint32_t),
                        k->share0[i]);
    mmio_region_write32(kmac->params.base_addr,
                        KMAC_KEY_SHARE1_0_REG_OFFSET + i * sizeof(uint32_t),
                        k->share1[i]);
  }

  // Configure cSHAKE mode with the given strength and enable KMAC mode.
  uint32_t cfg_reg =
      mmio_region_read32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_KMAC_EN_BIT, true);
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_KSTRENGTH_FIELD, kstrength);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_MODE_FIELD,
                                   KMAC_CFG_MODE_VALUE_CSHAKE);
  mmio_region_write32(kmac->params.base_addr, KMAC_CFG_REG_OFFSET, cfg_reg);

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
  const mmio_region_t base = kmac->params.base_addr;
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
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Poll until the status register is in the 'absorb' state.
  while (true) {
    if (is_state_absorb(kmac->params)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_absorb(dif_kmac_t *kmac, const void *msg, size_t len,
                                  size_t *processed) {
  // Set the number of bytes processed to 0.
  if (processed != NULL) {
    *processed = 0;
  }

  if (kmac == NULL || (msg == NULL && len != 0)) {
    return kDifKmacBadArg;
  }

  // Check that an operation has been started.
  if (kmac->r == 0) {
    return kDifKmacError;
  }

  // Poll until the the status register is in the 'absorb' state.
  if (!is_state_absorb(kmac->params)) {
    return kDifKmacError;
  }

  // Copy the message one byte at a time.
  // This could be sped up copying a word at a time but be careful
  // about message endianness (e.g. only copy a word at a time when in
  // little-endian mode).
  for (size_t i = 0; i < len; ++i) {
    mmio_region_write8(kmac->params.base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                       ((const uint8_t *)msg)[i]);
  }

  if (processed != NULL) {
    *processed = len;
  }
  return kDifKmacOk;
}

dif_kmac_result_t dif_kmac_squeeze(dif_kmac_t *kmac, uint32_t *out, size_t len,
                                   size_t *processed) {
  if (kmac == NULL || (out == NULL && len != 0)) {
    return kDifKmacBadArg;
  }

  // Set `processed` to 0 so we can return early without setting it again.
  if (processed != NULL) {
    *processed = 0;
  }

  const mmio_region_t base = kmac->params.base_addr;

  // Move into squeezing state (if not already in it).
  // Do this even if the length requested is 0 or too big.
  if (!kmac->squeezing) {
    if (kmac->append_d) {
      // The KMAC operation requires that the output length (d) in bits be right
      // encoded and appended to the end of the message.
      // Note: kDifKmacMaxOutputLenWords could be reduced to make this code
      // simpler. For example, a maximum of `(UINT16_MAX - 32) / 32` (just under
      // 8 KiB) would mean that d is guaranteed to be less than 0xFFFF.
      uint32_t d = kmac->d * 32;
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
    kmac->squeezing = true;

    // Issue squeeze command.
    uint32_t cmd_reg = bitfield_field32_write(0, KMAC_CMD_CMD_FIELD,
                                              KMAC_CMD_CMD_VALUE_PROCESS);
    mmio_region_write32(base, KMAC_CMD_REG_OFFSET, cmd_reg);
  }

  // If the operation has a fixed length output then the total number of bytes
  // requested must not exceed that length.
  if (kmac->d != 0 && len > (kmac->d - kmac->offset)) {
    return kDifKmacError;
  }

  if (len == 0) {
    return kDifKmacOk;
  }

  while (len > 0) {
    size_t n = len;
    size_t remaining = kmac->r - kmac->offset;
    if (kmac->d != 0 && kmac->d < kmac->r) {
      remaining = kmac->d - kmac->offset;
    }
    if (n > remaining) {
      n = remaining;
    }
    if (n == 0) {
      // Reduce the digest length to reflect consumed output state.
      if (kmac->d != 0) {
        if (kmac->d <= kmac->r) {
          return kDifKmacError;
        }
        kmac->d -= kmac->r;
      }

      // Issue run command to generate more state.
      uint32_t cmd_reg =
          bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_RUN);
      mmio_region_write32(base, KMAC_CMD_REG_OFFSET, cmd_reg);
      kmac->offset = 0;
      continue;
    }

    // Poll the status register until in the 'squeeze' state.
    while (true) {
      if (is_state_squeeze(kmac->params)) {
        break;
      }
      // TODO(#6248): check for error.
    }

    uint32_t offset = KMAC_STATE_REG_OFFSET + kmac->offset * sizeof(uint32_t);
    for (size_t i = 0; i < n; ++i) {
      // Read both shares from state register and combine using XOR.
      uint32_t share0 = mmio_region_read32(base, offset);
      uint32_t share1 =
          mmio_region_read32(base, offset + kDifKmacStateShareOffset);
      *out++ = share0 ^ share1;
      offset += sizeof(uint32_t);
    }
    kmac->offset += n;
    len -= n;
    if (processed != NULL) {
      *processed += n;
    }
  }
  return kDifKmacOk;
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
    if (is_state_squeeze(kmac->params)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  // Issue done command.
  uint32_t cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_DONE);
  mmio_region_write32(kmac->params.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);

  // Reset state.
  kmac->squeezing = false;
  kmac->append_d = false;
  kmac->offset = 0;
  kmac->r = 0;
  kmac->d = 0;

  // Poll status register until in idle state.
  while (true) {
    if (is_state_idle(kmac->params)) {
      break;
    }
    // TODO(#6248): check for error.
  }

  return kDifKmacOk;
}
