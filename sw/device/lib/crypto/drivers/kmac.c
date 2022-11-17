// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength128,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength224,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength256,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength384,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength512,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512);

OT_ASSERT_ENUM_VALUE(kKmacKeyLength128, KMAC_KEY_LEN_LEN_VALUE_KEY128);
OT_ASSERT_ENUM_VALUE(kKmacKeyLength192, KMAC_KEY_LEN_LEN_VALUE_KEY192);
OT_ASSERT_ENUM_VALUE(kKmacKeyLength256, KMAC_KEY_LEN_LEN_VALUE_KEY256);
OT_ASSERT_ENUM_VALUE(kKmacKeyLength384, KMAC_KEY_LEN_LEN_VALUE_KEY384);
OT_ASSERT_ENUM_VALUE(kKmacKeyLength512, KMAC_KEY_LEN_LEN_VALUE_KEY512);

enum {
  kKmacPrefixRegCount = 4 * KMAC_PREFIX_MULTIREG_COUNT,
  // The total size of prefix registers (in bytes), after removing len encodings
  kKmacPrefixMaxSize = 4 * KMAC_PREFIX_MULTIREG_COUNT - 4,
  kKmacBaseAddr = TOP_EARLGREY_KMAC_BASE_ADDR,
  kKmacCfgAddr = kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET,
  kKmacKeyShare0Addr = kKmacBaseAddr + KMAC_KEY_SHARE0_0_REG_OFFSET,
  kKmacKeyShare1Addr = kKmacBaseAddr + KMAC_KEY_SHARE1_0_REG_OFFSET,
};

OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength128,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength224,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength256,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength384,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384);
OT_ASSERT_ENUM_VALUE(kKmacSecurityStrength512,
                     KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512);

static const uint32_t prefix_offsets[] = {
    KMAC_PREFIX_0_REG_OFFSET,  KMAC_PREFIX_1_REG_OFFSET,
    KMAC_PREFIX_2_REG_OFFSET,  KMAC_PREFIX_3_REG_OFFSET,
    KMAC_PREFIX_4_REG_OFFSET,  KMAC_PREFIX_5_REG_OFFSET,
    KMAC_PREFIX_6_REG_OFFSET,  KMAC_PREFIX_7_REG_OFFSET,
    KMAC_PREFIX_8_REG_OFFSET,  KMAC_PREFIX_9_REG_OFFSET,
    KMAC_PREFIX_10_REG_OFFSET,
};

// Check that KEY_SHARE registers form a continuous address space
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_1_REG_OFFSET,
                     KMAC_KEY_SHARE0_0_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_2_REG_OFFSET,
                     KMAC_KEY_SHARE0_1_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_3_REG_OFFSET,
                     KMAC_KEY_SHARE0_2_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_4_REG_OFFSET,
                     KMAC_KEY_SHARE0_3_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_5_REG_OFFSET,
                     KMAC_KEY_SHARE0_4_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_6_REG_OFFSET,
                     KMAC_KEY_SHARE0_5_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_7_REG_OFFSET,
                     KMAC_KEY_SHARE0_6_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_8_REG_OFFSET,
                     KMAC_KEY_SHARE0_7_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_9_REG_OFFSET,
                     KMAC_KEY_SHARE0_8_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_10_REG_OFFSET,
                     KMAC_KEY_SHARE0_9_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_11_REG_OFFSET,
                     KMAC_KEY_SHARE0_10_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_12_REG_OFFSET,
                     KMAC_KEY_SHARE0_11_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_13_REG_OFFSET,
                     KMAC_KEY_SHARE0_12_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_14_REG_OFFSET,
                     KMAC_KEY_SHARE0_13_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE0_15_REG_OFFSET,
                     KMAC_KEY_SHARE0_14_REG_OFFSET + 4);

OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_1_REG_OFFSET,
                     KMAC_KEY_SHARE1_0_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_2_REG_OFFSET,
                     KMAC_KEY_SHARE1_1_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_3_REG_OFFSET,
                     KMAC_KEY_SHARE1_2_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_4_REG_OFFSET,
                     KMAC_KEY_SHARE1_3_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_5_REG_OFFSET,
                     KMAC_KEY_SHARE1_4_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_6_REG_OFFSET,
                     KMAC_KEY_SHARE1_5_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_7_REG_OFFSET,
                     KMAC_KEY_SHARE1_6_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_8_REG_OFFSET,
                     KMAC_KEY_SHARE1_7_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_9_REG_OFFSET,
                     KMAC_KEY_SHARE1_8_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_10_REG_OFFSET,
                     KMAC_KEY_SHARE1_9_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_11_REG_OFFSET,
                     KMAC_KEY_SHARE1_10_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_12_REG_OFFSET,
                     KMAC_KEY_SHARE1_11_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_13_REG_OFFSET,
                     KMAC_KEY_SHARE1_12_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_14_REG_OFFSET,
                     KMAC_KEY_SHARE1_13_REG_OFFSET + 4);
OT_ASSERT_ENUM_VALUE(KMAC_KEY_SHARE1_15_REG_OFFSET,
                     KMAC_KEY_SHARE1_14_REG_OFFSET + 4);

OT_ASSERT_ENUM_VALUE(ARRAYSIZE(prefix_offsets), KMAC_PREFIX_MULTIREG_COUNT);
OT_ASSERT_ENUM_VALUE(32, KMAC_PREFIX_PREFIX_FIELD_WIDTH);

/**
 * Return the rate (in bytes) for given security strength.
 *
 * @param sec_str Security strength.
 * @param keccak_rate The keccak rate in bytes.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static kmac_error_t kmac_get_keccak_rate_bytes(uint32_t security_str,
                                               size_t *keccak_rate) {
  if (keccak_rate == NULL) {
    return kKmacArgsError;
  }

  // Since Keccak state is 1600 bits, rate is calculated with
  // rate = (1600 - 2*x) where x is the security strength (i.e. half the
  // capacity).
  switch (security_str) {
    case kKmacSecurityStrength128:
      *keccak_rate = 168;
      break;
    case kKmacSecurityStrength224:
      *keccak_rate = 144;
      break;
    case kKmacSecurityStrength256:
      *keccak_rate = 136;
      break;
    case kKmacSecurityStrength384:
      *keccak_rate = 104;
      break;
    case kKmacSecurityStrength512:
      *keccak_rate = 72;
      break;
    default:
      return kKmacArgsError;
  }
  return kKmacOk;
}

/**
 * Return the key length (in bytes) for kmac_key_len_t enum value.
 *
 * @param key_len kmac_key_len_t enum value as input.
 * @param key_len_bytes The length of the key in bytes.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static kmac_error_t kmac_get_key_len_bytes(kmac_key_len_t key_len,
                                           size_t *key_len_bytes) {
  if (key_len_bytes == NULL) {
    return kKmacArgsError;
  }

  switch (key_len) {
    case kKmacKeyLength128:
      *key_len_bytes = 16;
      break;
    case kKmacKeyLength192:
      *key_len_bytes = 24;
      break;
    case kKmacKeyLength256:
      *key_len_bytes = 32;
      break;
    case kKmacKeyLength384:
      *key_len_bytes = 48;
      break;
    case kKmacKeyLength512:
      *key_len_bytes = 64;
      break;
    default:
      return kKmacArgsError;
  }
  return kKmacOk;
}

kmac_error_t kmac_hwip_default_configure(void) {
  uint32_t status_reg = abs_mmio_read32(kKmacBaseAddr + KMAC_STATUS_REG_OFFSET);

  // Check that core is not in fault state
  if (bitfield_bit32_read(status_reg, KMAC_STATUS_ALERT_FATAL_FAULT_BIT)) {
    return kKmacFatalFaultError;
  }
  if (bitfield_bit32_read(status_reg,
                          KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT)) {
    return kKmacRecovFaultError;
  }
  // Check that core is not busy
  if (!bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_IDLE_BIT)) {
    return kKmacNotIdle;
  }

  // Check that there is no err pending in intr state
  uint32_t intr_state =
      abs_mmio_read32(kKmacBaseAddr + KMAC_INTR_STATE_REG_OFFSET);
  if (bitfield_bit32_read(intr_state, KMAC_INTR_STATE_KMAC_ERR_BIT)) {
    return kKmacIntrErrPending;
  }

  // Check CFG.regwen
  uint32_t cfg_regwen =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(cfg_regwen, KMAC_CFG_REGWEN_EN_BIT)) {
    return kKmacCfgWriteDisabled;
  }

  // Keep err interrupt disabled
  uint32_t intr_reg = KMAC_INTR_ENABLE_REG_RESVAL;
  intr_reg = bitfield_bit32_write(intr_reg, KMAC_INTR_ENABLE_KMAC_ERR_BIT, 0);
  abs_mmio_write32(kKmacBaseAddr + KMAC_INTR_ENABLE_REG_OFFSET, intr_reg);

  // Configure max for entropy period (use UINT32_MAX and let bitfield clamp
  // them to their bitfield)
  uint32_t entropy_period = KMAC_ENTROPY_PERIOD_REG_RESVAL;
  entropy_period = bitfield_field32_write(
      entropy_period, KMAC_ENTROPY_PERIOD_PRESCALER_FIELD, UINT32_MAX);
  entropy_period = bitfield_field32_write(
      entropy_period, KMAC_ENTROPY_PERIOD_WAIT_TIMER_FIELD, UINT32_MAX);
  abs_mmio_write32(kKmacBaseAddr + KMAC_ENTROPY_PERIOD_REG_OFFSET,
                   entropy_period);

  // Configure max for hash threshold (use UINT32_MAX and let bitfield clamp
  // them to their bitfield)
  uint32_t entropy_hash_threshold =
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_RESVAL;
  entropy_hash_threshold = bitfield_field32_write(
      entropy_hash_threshold,
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_THRESHOLD_FIELD, UINT32_MAX);
  abs_mmio_write32(
      kKmacBaseAddr + KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_OFFSET,
      entropy_hash_threshold);

  // Configure CFG
  uint32_t cfg_reg = KMAC_CFG_SHADOWED_REG_RESVAL;
  // Little_endian
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT, 0);
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT, 0);

  // Sideload: off, default key comes from SW
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT, 0);

  // Entropy mode: EDN
  cfg_reg =
      bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_MODE_FIELD,
                             KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_EDN_MODE);

  // Use quality randomness for message blocks too
  cfg_reg = bitfield_bit32_write(cfg_reg,
                                 KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT, 1);
  // Do not remask message blocks
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_MASK_BIT, 0);

  // Mark entropy source as ready
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, 1);
  // Err not processed
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ERR_PROCESSED_BIT, 0);
  // Unsupported modes: disabled
  cfg_reg = bitfield_bit32_write(
      cfg_reg, KMAC_CFG_SHADOWED_EN_UNSUPPORTED_MODESTRENGTH_BIT, 0);

  abs_mmio_write32_shadowed(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET,
                            cfg_reg);

  return kKmacOk;
}

/**
 * Wait until given status bit is set.
 *
 * Loops until the `bit_position` of status register reaches the value
 * `bit_value`.
 * @param bit_position The bit position in the status register.
 * @param bit_value Whether it should wait for 0 or 1.
 */
OT_WARN_UNUSED_RESULT
static kmac_error_t wait_status_bit(uint32_t bit_position, bool bit_value) {
  if (bit_position > 31) {
    return kKmacArgsError;
  }

  while (true) {
    uint32_t reg = abs_mmio_read32(kKmacBaseAddr + KMAC_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, KMAC_STATUS_ALERT_FATAL_FAULT_BIT) ||
        bitfield_bit32_read(reg, KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT)) {
      return kKmacInternalError;
    }
    if (bitfield_bit32_read(reg, bit_position) == bit_value) {
      return kKmacOk;
    }
  }
}

/**
 * Encode a given integer as byte array and return its size along with it.
 *
 * This is a common procedure that can be used to implement both `left_encode`
 * and `right_encode` functions defined in NIST SP 800-185. Given an integer
 * `value` it returns its encoding as a byte array in `encoding_buf`. Meanwhile,
 * `encoding_header` keeps the size of `encoding_buf`. Later the two can be
 * combined as below:
 *
 * left_encode(`value`) = `encoding_header` || `encoding_buf`
 * right_encode(`value`) = `encoding_buf` || `encoding_header`
 *
 * @param value Integer to be encoded.
 * @param encoding_buf The output byte array representing `value`.
 * @param encoding_header The number of bytes written to `encoded_value`.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static kmac_error_t little_endian_encode(size_t value, uint8_t *encoding_buf,
                                         uint8_t *encoding_header) {
  if (encoding_buf == NULL || encoding_header == NULL) {
    return kKmacArgsError;
  }

  uint8_t len = 0;
  do {
    encoding_buf[len] = value & UINT8_MAX;
    value >>= 8;
    len++;
  } while (value > 0);
  *encoding_header = len;

  return kKmacOk;
}

/**
 * Set prefix registers.
 *
 * This function directly writes to PREFIX registers of KMAC HWIP.
 *
 * @param func_name Function name input in cSHAKE.
 * @param func_name_len The number of valid bytes in `func_name` buffer.
 * @param cust_str Customization string input in cSHAKE.
 * @param cust_str_len The number of valid bytes in `cust_str` buffer.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static kmac_error_t kmac_set_prefix_regs(const uint8_t *func_name,
                                         const size_t func_name_len,
                                         const uint8_t *cust_str,
                                         const size_t cust_str_len) {
  // static_assert(kKmacPrefixMaxSize < 8192, ");

  // Initialize with 0 so that the last untouched bytes are set as 0x0
  uint32_t prefix_buffer[kKmacPrefixRegCount] = {0x0};
  uint8_t *prefix_buf_ptr = (uint8_t *)prefix_buffer;

  if ((cust_str_len && cust_str == NULL) ||
      (func_name_len && func_name == NULL)) {
    return kKmacArgsError;
  } else if (func_name_len + cust_str_len > kKmacPrefixMaxSize) {
    return kKmacArgsError;
  }

  size_t func_name_len_bits = 8 * func_name_len;
  size_t cust_str_len_bits = 8 * cust_str_len;
  size_t i = 0;
  size_t write_cnt = 0;
  uint8_t j = 0;
  kmac_error_t err;

  // left_encode(`func_name_len_bits`) below
  err = little_endian_encode(func_name_len_bits, prefix_buf_ptr + 1, &j);
  if (err != kKmacOk) {
    return err;
  }
  prefix_buf_ptr[0] = j;
  write_cnt += j + 1;

  // copy func_name
  memcpy(prefix_buf_ptr + write_cnt, func_name, func_name_len);

  write_cnt += func_name_len;

  // left_encode(`cust_str_len_bits`) below
  err = little_endian_encode(cust_str_len_bits, prefix_buf_ptr + write_cnt + 1,
                             &j);
  if (err != kKmacOk) {
    return err;
  }

  // copy cust_str
  prefix_buf_ptr[write_cnt] = j;
  write_cnt += j + 1;
  memcpy(prefix_buf_ptr + write_cnt, cust_str, cust_str_len);

  // Copy from `prefix_buffer` to PREFIX_REGS
  for (i = 0; i < KMAC_PREFIX_MULTIREG_COUNT; i++) {
    abs_mmio_write32(kKmacBaseAddr + prefix_offsets[i], prefix_buffer[i]);
  }

  return kKmacOk;
}

kmac_error_t kmac_init(kmac_operation_t operation,
                       kmac_security_str_t security_str,
                       const uint8_t *func_name, uint8_t func_name_len,
                       const uint8_t *cust_str, size_t cust_str_len) {
  if (cust_str_len && cust_str == NULL) {
    return kKmacArgsError;
  } else if (func_name_len && func_name == NULL) {
    return kKmacArgsError;
  }

  if (cust_str_len + func_name_len > kKmacPrefixMaxSize) {
    return kKmacArgsError;
  }

  kmac_error_t err = wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1);
  if (err != kKmacOk) {
    return err;
  }

  uint32_t cfg_reg =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET);

  switch (operation) {
    case kKmacOperationSHA3:
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHA3);
      break;
    case kKmacOperationSHAKE:
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE);
      break;
    case kKmacOperationKMAC:
      // For KMAC HWIP, KMAC is not defined as a mode at the hardware level so
      // we need to use mode=cSHAKE and enable KMAC_EN_BIT to run KMAC
      cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, 1);
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE);
      break;
    case kKmacOperationCSHAKE:
      cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                       KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE);
      break;
    default:
      return kKmacArgsError;
  }

  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   security_str);
  abs_mmio_write32_shadowed(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET,
                            cfg_reg);

  return kKmacOk;
}

kmac_error_t kmac_write_prefix_block(kmac_operation_t operation,
                                     const uint8_t *func_name,
                                     const size_t func_name_len,
                                     const uint8_t *cust_str,
                                     const size_t cust_str_len) {
  kmac_error_t err = kKmacOk;
  // Write to prefix registers
  if (operation == kKmacOperationCSHAKE) {
    err =
        kmac_set_prefix_regs(func_name, func_name_len, cust_str, cust_str_len);
  } else if (operation == kKmacOperationKMAC) {
    uint8_t kmac_func_name[4] = {0x4b, 0x4d, 0x41,
                                 0x43};  // "KMAC" in little endian
    err = kmac_set_prefix_regs(kmac_func_name, /*func_name_len=*/4, cust_str,
                               cust_str_len);
  }
  if (err != kKmacOk) {
    return err;
  }
  return err;
}

kmac_error_t kmac_write_key_block(const uint8_t *key, kmac_key_len_t key_len) {
  if (key == NULL) {
    return kKmacArgsError;
  }

  uint32_t key_len_reg = KMAC_KEY_LEN_REG_RESVAL;
  key_len_reg =
      bitfield_field32_write(key_len_reg, KMAC_KEY_LEN_LEN_FIELD, key_len);
  abs_mmio_write32(kKmacBaseAddr + KMAC_KEY_LEN_REG_OFFSET, key_len_reg);

  size_t key_len_bytes;
  kmac_error_t err = kmac_get_key_len_bytes(key_len, &key_len_bytes);
  if (err != kKmacOk) {
    return err;
  }

  uint32_t *word_ptr = (uint32_t *)key;
  for (size_t i = 0; i < key_len_bytes; i += 4) {
    abs_mmio_write32(kKmacKeyShare0Addr + i, *word_ptr++);
    abs_mmio_write32(kKmacKeyShare1Addr + i, 0x00);
  }

  return kKmacOk;
}

kmac_error_t kmac_process_msg_blocks(kmac_operation_t operation,
                                     const uint8_t *data, size_t data_len,
                                     uint8_t *digest, size_t digest_len) {
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  kmac_error_t err;

  // Assumption(1): `data_len` > 0 and `digest_len` > 0
  // Assumption(2): data % 4 = 0, i.e. the data ptr is 32-bit aligned

  err = wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1);
  // Issue the start command, so that messages written to MSG_FIFO are forwarded
  // to Keccak
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_START);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);
  err = wait_status_bit(KMAC_STATUS_SHA3_ABSORB_BIT, 1);
  if (err != kKmacOk) {
    return err;
  }

  // Begin by writing a word at a time
  uint32_t *word_ptr = (uint32_t *)data;
  size_t i = 0;
  for (; i < data_len / 4; i++) {
    err = wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0);
    if (err != kKmacOk) {
      return err;
    }
    abs_mmio_write32(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET, word_ptr[i]);
  }

  // For the last few bytes, we need to write byte at a time
  // i = 4*(data_len/4)
  for (i = 4 * i; i < data_len; i++) {
    err = wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0);
    if (err != kKmacOk) {
      return err;
    }
    abs_mmio_write8(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET + (i % 4),
                    data[i]);
  }

  // If operation=KMAC, then we need to write `right_encode(digest_len)`
  if (operation == kKmacOperationKMAC) {
    uint32_t digest_len_bits = 8 * digest_len;
    if (digest_len_bits / 8 != digest_len) {
      return kKmacDigestLenTooLongError;
    }

    // right_encode(`digest_len_bit`) below
    // The encoded buffer in total occupies at most 256 bytes according to
    // NIST SP 800-185 (1 byte for encoding header and 255 byte for the encoded
    // buffer at max)
    uint8_t buf[256] = {0};
    uint8_t encoding_header;
    err = little_endian_encode(digest_len_bits, buf, &encoding_header);
    if (err != kKmacOk) {
      return err;
    }
    buf[encoding_header] = encoding_header;

    // Because the MSG_FIFO is also little endian we need to write in reverse
    // order
    for (size_t i = 0; i < encoding_header; i++) {
      abs_mmio_write8(
          kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET + ((data_len + i) % 4),
          buf[encoding_header - i - 1]);
    }

    // Finally write `encoding_header` as the last byte
    abs_mmio_write8(
        kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET + ((data_len + i) % 4),
        buf[encoding_header]);
  }

  // Issue the process command, so that squeezing phase can start
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_PROCESS);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);

  // Wait until squeezing is done
  err = wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1);
  if (err != kKmacOk) {
    return err;
  }

  uint32_t cfg_reg =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET);
  uint32_t keccak_str =
      bitfield_field32_read(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD);
  size_t keccak_rate;
  err = kmac_get_keccak_rate_bytes(keccak_str, &keccak_rate);
  if (err != kKmacOk) {
    return err;
  }

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
      abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);

      // Let Keccak core finish the extra squeezing round
      err = wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1);
      if (err != kKmacOk) {
        return err;
      }
    }
    digest[i] = abs_mmio_read8(kKmacBaseAddr + KMAC_STATE_REG_OFFSET +
                               (i % keccak_rate));
    digest[i] ^= abs_mmio_read8(kKmacBaseAddr + KMAC_STATE_REG_OFFSET +
                                KMAC_STATE_SIZE_BYTES / 2 + (i % keccak_rate));
  }

  // Release the KMAC core, so that it goes back to idle mode
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_DONE);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);
  if (err != kKmacOk) {
    return err;
  }

  return kKmacOk;
}
