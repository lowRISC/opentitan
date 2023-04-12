// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'k', 'm')

/**
 * Security strength values.
 *
 * These values corresponds to the half of the capacity of Keccak permutation.
 */
typedef enum kmac_security_str {
  kKmacSecurityStrength128 = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128,
  kKmacSecurityStrength224 = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224,
  kKmacSecurityStrength256 = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256,
  kKmacSecurityStrength384 = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L384,
  kKmacSecurityStrength512 = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L512,
} kmac_security_str_t;

/**
 * List of supported KMAC modes.
 *
 * Each `kmac_operation_t` enumeration constant is a bitfield with the
 * following layout:
 * - Bit 0: kmac_en (Whether to enable KMAC datapath).
 * - Bit 1-2: Keccak hashing mode (e.g. SHA, SHAKE, or cSHAKE).
 */
typedef enum kmac_operation {
  kKmacOperationSHA3 = KMAC_CFG_SHADOWED_MODE_VALUE_SHA3 << 1 | 0,
  kKmacOperationSHAKE = KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE << 1 | 0,
  kKmacOperationCSHAKE = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE << 1 | 0,
  kKmacOperationKMAC = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE << 1 | 1,
} kmac_operation_t;

/**
 * List of supported KMAC key sizes.
 */
typedef enum kmac_key_length {
  kKmacKeyLength128 = KMAC_KEY_LEN_LEN_VALUE_KEY128,
  kKmacKeyLength192 = KMAC_KEY_LEN_LEN_VALUE_KEY192,
  kKmacKeyLength256 = KMAC_KEY_LEN_LEN_VALUE_KEY256,
  kKmacKeyLength384 = KMAC_KEY_LEN_LEN_VALUE_KEY384,
  kKmacKeyLength512 = KMAC_KEY_LEN_LEN_VALUE_KEY512,
} kmac_key_len_t;

enum {
  kKmacPrefixRegCount = 4 * KMAC_PREFIX_MULTIREG_COUNT,
  kKmacBaseAddr = TOP_EARLGREY_KMAC_BASE_ADDR,
  kKmacCfgAddr = kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET,
  kKmacKeyShare0Addr = kKmacBaseAddr + KMAC_KEY_SHARE0_0_REG_OFFSET,
  kKmacKeyShare1Addr = kKmacBaseAddr + KMAC_KEY_SHARE1_0_REG_OFFSET,
};

// "KMAC" string in little endian
static const crypto_const_uint8_buf_t kKmacFuncNameKMAC = {
    .data = (uint8_t *)"\x4b\x4d\x41\x43",
    .len = 4,
};

// Empty string
static const crypto_const_uint8_buf_t kKmacEmptyString = {
    .data = NULL,
    .len = 0,
};

OT_ASSERT_ENUM_VALUE(kKmacPrefixMaxSize, 4 * KMAC_PREFIX_MULTIREG_COUNT - 4);

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

// Ensure each PREFIX register is 4 bytes
OT_ASSERT_ENUM_VALUE(32, KMAC_PREFIX_PREFIX_FIELD_WIDTH);

/**
 * Return the rate (in bytes) for given security strength.
 *
 * The caller must ensure that `keccak_rate` is not a NULL pointer. This is not
 * checked within this function.
 *
 * @param security_str Security strength.
 * @param keccak_rate The keccak rate in bytes.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_get_keccak_rate_bytes(kmac_security_str_t security_str,
                                           size_t *keccak_rate) {
  // Since Keccak state is 1600 bits, rate is calculated with
  // rate = (1600 - 2*x) where x is the security strength (i.e. half the
  // capacity). Here, `keccak_rate` is in bytes.
  switch (security_str) {
    case kKmacSecurityStrength128:
      *keccak_rate = (1600 - 2 * 128) / 8;
      break;
    case kKmacSecurityStrength224:
      *keccak_rate = (1600 - 2 * 224) / 8;
      break;
    case kKmacSecurityStrength256:
      *keccak_rate = (1600 - 2 * 256) / 8;
      break;
    case kKmacSecurityStrength384:
      *keccak_rate = (1600 - 2 * 384) / 8;
      break;
    case kKmacSecurityStrength512:
      *keccak_rate = (1600 - 2 * 512) / 8;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Return the matching enum of `kmac_key_len_t` for given key length.
 *
 * `key_len_enum` must not be NULL pointer.
 *
 * @param key_len The size of the key in bytes.
 * @param key_len_enum The corresponding enum value to be returned.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_get_key_len_bytes(size_t key_len,
                                       kmac_key_len_t *key_len_enum) {
  switch (key_len) {
    case 128 / 8:
      *key_len_enum = kKmacKeyLength128;
      break;
    case 192 / 8:
      *key_len_enum = kKmacKeyLength192;
      break;
    case 256 / 8:
      *key_len_enum = kKmacKeyLength256;
      break;
    case 384 / 8:
      *key_len_enum = kKmacKeyLength384;
      break;
    case 512 / 8:
      *key_len_enum = kKmacKeyLength512;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

status_t kmac_key_length_check(size_t key_len) {
  kmac_key_len_t key_len_enum;
  // Run the conversion to the key length enum, but we only care about the
  // error code.
  return kmac_get_key_len_bytes(key_len, &key_len_enum);
}

status_t kmac_hwip_default_configure(void) {
  uint32_t status_reg = abs_mmio_read32(kKmacBaseAddr + KMAC_STATUS_REG_OFFSET);

  // Check that core is not in fault state
  if (bitfield_bit32_read(status_reg, KMAC_STATUS_ALERT_FATAL_FAULT_BIT)) {
    return OTCRYPTO_FATAL_ERR;
  }
  if (bitfield_bit32_read(status_reg,
                          KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }
  // Check that core is not busy
  if (!bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_IDLE_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  // Check that there is no err pending in intr state
  uint32_t intr_state =
      abs_mmio_read32(kKmacBaseAddr + KMAC_INTR_STATE_REG_OFFSET);
  if (bitfield_bit32_read(intr_state, KMAC_INTR_STATE_KMAC_ERR_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  // Check CFG.regwen
  uint32_t cfg_regwen =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(cfg_regwen, KMAC_CFG_REGWEN_EN_BIT)) {
    return OTCRYPTO_RECOV_ERR;
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

  return OTCRYPTO_OK;
}

/**
 * Wait until given status bit is set.
 *
 * Loops until the `bit_position` of status register reaches the value
 * `bit_value`.
 * @param bit_position The bit position in the status register.
 * @param bit_value Whether it should wait for 0 or 1.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
static status_t wait_status_bit(uint32_t bit_position, bool bit_value) {
  if (bit_position > 31) {
    return OTCRYPTO_BAD_ARGS;
  }

  while (true) {
    uint32_t reg = abs_mmio_read32(kKmacBaseAddr + KMAC_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, KMAC_STATUS_ALERT_FATAL_FAULT_BIT)) {
      return OTCRYPTO_FATAL_ERR;
    }
    if (bitfield_bit32_read(reg, KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT)) {
      return OTCRYPTO_RECOV_ERR;
    }
    if (bitfield_bit32_read(reg, bit_position) == bit_value) {
      return OTCRYPTO_OK;
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
 * The caller must ensure that `encoding_buf` and `encoding_header` are not
 * NULL pointers. This is not checked within this function.
 *
 * @param value Integer to be encoded.
 * @param encoding_buf The output byte array representing `value`.
 * @param encoding_header The number of bytes written to `encoded_value`.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t little_endian_encode(size_t value, uint8_t *encoding_buf,
                                     uint8_t *encoding_header) {
  uint8_t len = 0;
  do {
    encoding_buf[len] = value & UINT8_MAX;
    value >>= 8;
    len++;
  } while (value > 0);
  *encoding_header = len;

  return OTCRYPTO_OK;
}

/**
 * Set prefix registers.
 *
 * This function directly writes to PREFIX registers of KMAC HWIP.
 *
 * @param func_name Function name input in cSHAKE.
 * @param cust_str Customization string input in cSHAKE.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_set_prefix_regs(crypto_const_uint8_buf_t func_name,
                                     crypto_const_uint8_buf_t cust_str) {
  // Initialize with 0 so that the last untouched bytes are set as 0x0
  uint32_t prefix_buffer[kKmacPrefixRegCount] = {0x0};
  uint8_t *prefix_buf_ptr = (uint8_t *)prefix_buffer;

  if (func_name.len + cust_str.len > kKmacPrefixMaxSize) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t func_name_len_bits = 8 * func_name.len;
  size_t cust_str_len_bits = 8 * cust_str.len;
  size_t i = 0;
  size_t write_cnt = 0;
  uint8_t j = 0;

  // left_encode(`func_name_len_bits`) below
  HARDENED_TRY(
      little_endian_encode(func_name_len_bits, prefix_buf_ptr + 1, &j));
  prefix_buf_ptr[0] = j;
  write_cnt += j + 1;

  // copy `func_name`
  memcpy(prefix_buf_ptr + write_cnt, func_name.data, func_name.len);

  write_cnt += func_name.len;

  // left_encode(`cust_str_len_bits`) below
  HARDENED_TRY(little_endian_encode(cust_str_len_bits,
                                    prefix_buf_ptr + write_cnt + 1, &j));

  // copy `cust_str`
  prefix_buf_ptr[write_cnt] = j;
  write_cnt += j + 1;
  memcpy(prefix_buf_ptr + write_cnt, cust_str.data, cust_str.len);

  // Copy from `prefix_buffer` to PREFIX_REGS
  for (i = 0; i < KMAC_PREFIX_MULTIREG_COUNT; i++) {
    abs_mmio_write32(kKmacBaseAddr + prefix_offsets[i], prefix_buffer[i]);
  }

  return OTCRYPTO_OK;
}

/**
 * Initializes the KMAC configuration.
 *
 * In particular, this function sets the CFG register of KMAC for given
 * `operation_type`. The struct type kmac_operation_t is defined in a way that
 * each field inherently implies a fixed security strength (i.e. half of Keccak
 * capacity). For instance, if we want to run SHA-3 with 224-bit digest size,
 * then `operation_type` = kSHA3_224.
 *
 *
 * @param operation The chosen operation, see kmac_operation_t struct.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_init(kmac_operation_t operation,
                          kmac_security_str_t security_str) {
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));

  // We need to preserve some bits of CFG register, such as:
  // entropy_mode, entropy_ready etc. On the other hand, some bits
  // need to be reset for each invocation.
  uint32_t cfg_reg =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET);

  // Make sure kmac_en and sideload bits of CFG are reset at each invocation
  // These bits should be set to 1 only if needed by the rest of the code
  // in this function.
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, 0);
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT, 0);

  // operation bit fields: Bit 0: `kmac_en`, Bit 1-2: `mode`
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT,
                                 operation & 1);
  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_MODE_FIELD,
                                   operation >> 1);

  cfg_reg = bitfield_field32_write(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD,
                                   security_str);
  abs_mmio_write32_shadowed(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET,
                            cfg_reg);

  return OTCRYPTO_OK;
}

/**
 * Configure the prefix registers with customization string.
 *
 * For KMAC, this function ignores `func_name` and uses "KMAC" instead.
 *
 * The caller must ensure that `func_name` and `cust_str` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * In total `func_name` and `cust_str` can be at most `kKmacPrefixMaxSize`
 * bytes.
 *
 * @param operation The KMAC or cSHAKE operation.
 * @param func_name The function name, used for cSHAKE.
 * @param cust_str The customization string (both for cSHAKE and KMAC).
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_write_prefix_block(kmac_operation_t operation,
                                        crypto_const_uint8_buf_t func_name,
                                        crypto_const_uint8_buf_t cust_str) {
  if (operation == kKmacOperationCSHAKE) {
    return kmac_set_prefix_regs(func_name, cust_str);
  } else if (operation == kKmacOperationKMAC) {
    return kmac_set_prefix_regs(/*func_name=*/kKmacFuncNameKMAC, cust_str);
  }
  return OTCRYPTO_BAD_ARGS;
}

/**
 * Update the key registers with given key shares.
 *
 * The caller must ensure that `key` struct is properly populated (no NULL
 * pointers and matching `len`).
 *
 * The accepted `key->len` values are {128 / 8, 192 / 8, 256 / 8, 384 / 8,
 * 512 / 8}, otherwise an error will be returned.
 *
 * @param key The input key passed as a struct.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_write_key_block(kmac_blinded_key_t *key) {
  kmac_key_len_t key_len_enum;
  HARDENED_TRY(kmac_get_key_len_bytes(key->len, &key_len_enum));

  uint32_t key_len_reg = bitfield_field32_write(
      KMAC_KEY_LEN_REG_RESVAL, KMAC_KEY_LEN_LEN_FIELD, key_len_enum);
  abs_mmio_write32(kKmacBaseAddr + KMAC_KEY_LEN_REG_OFFSET, key_len_reg);

  for (size_t i = 0; i < key->len; i += 4) {
    abs_mmio_write32(kKmacKeyShare0Addr + i, key->share0[i / 4]);
    abs_mmio_write32(kKmacKeyShare1Addr + i, key->share1[i / 4]);
  }

  return OTCRYPTO_OK;
}

/**
 * Common routine for feeding message blocks during SHA/SHAKE/cSHAKE/KMAC.
 *
 * Before running this, the operation type must be configured with kmac_init.
 * Then, we can use this function to feed various bytes of data to the KMAC
 * core. Note that this is a one-shot implementation, and it does not support
 * streaming mode. This decision is in accord with OpenTitan's Crypto Library
 * Specification. Refer to the Hash section of this specification.
 *
 * Current implementation has few limitiations:
 *
 * 1. `message.data` pointer is assumed to be word-aligned. The case where
 * `data` field is not divisible by 4 is not yet implemented. This is about
 * extra protection against SCA.
 *
 * 2. Currently, there is no error check on consisteny of the input parameters.
 * For instance, one can invoke SHA-3_224 with digest_len=32, which will produce
 * 256 bits of digest.
 *
 * The caller must ensure that `message` and `digest` have properly
 * allocated `data` fields whose length matches their `len` fields.
 *
 * @param operation The operation type.
 * @param message Input message string.
 * @param digest The struct to which the result will be written.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_process_msg_blocks(kmac_operation_t operation,
                                        crypto_const_uint8_buf_t message,
                                        crypto_uint8_buf_t *digest) {
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;

  // Assumption(1): `message.len` > 0 and `digest->len` > 0
  // Assumption(2): message.data % 4 = 0, i.e. the message.data is 32-bit
  // aligned

  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));
  // Issue the start command, so that messages written to MSG_FIFO are forwarded
  // to Keccak
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_START);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_ABSORB_BIT, 1));

  // Begin by writing a word at a time
  uint32_t *word_ptr = (uint32_t *)message.data;
  size_t i = 0;
  for (; i < message.len / 4; i++) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    abs_mmio_write32(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET, word_ptr[i]);
  }

  // For the last few bytes, we need to write byte at a time
  // i = 4*(message.len/4)
  for (i = 4 * i; i < message.len; i++) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    abs_mmio_write8(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET + (i % 4),
                    message.data[i]);
  }

  // If operation=KMAC, then we need to write `right_encode(digest->len)`
  if (operation == kKmacOperationKMAC) {
    uint32_t digest_len_bits = 8 * digest->len;
    if (digest_len_bits / 8 != digest->len) {
      return OTCRYPTO_BAD_ARGS;
    }

    // right_encode(`digest_len_bit`) below
    // The encoded buffer in total occupies at most 256 bytes according to
    // NIST SP 800-185 (1 byte for encoding header and 255 byte for the encoded
    // buffer at max)
    uint8_t buf[256] = {0};
    uint8_t encoding_header;
    HARDENED_TRY(little_endian_encode(digest_len_bits, buf, &encoding_header));
    buf[encoding_header] = encoding_header;

    // Because the MSG_FIFO is also little endian we need to write in reverse
    // order
    for (size_t i = 0; i < encoding_header; i++) {
      abs_mmio_write8(
          kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET + ((message.len + i) % 4),
          buf[encoding_header - i - 1]);
    }

    // Finally write `encoding_header` as the last byte
    abs_mmio_write8(
        kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET + ((message.len + i) % 4),
        buf[encoding_header]);
  }

  // Issue the process command, so that squeezing phase can start
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_PROCESS);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);

  // Wait until squeezing is done
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

  uint32_t cfg_reg =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET);
  uint32_t keccak_str =
      bitfield_field32_read(cfg_reg, KMAC_CFG_SHADOWED_KSTRENGTH_FIELD);
  size_t keccak_rate;
  HARDENED_TRY(kmac_get_keccak_rate_bytes(keccak_str, &keccak_rate));

  // Finally, we can read the two shares of digest and XOR them
  // Here the counter i denotes the number of bytes read from Keccak state
  for (i = 0; i < digest->len; i++) {
    // Do we require additional Keccak rounds?
    if ((i % keccak_rate) == 0 && i > 0) {
      // if we consumed all Keccak state and aren't done yet, run one more
      // Keccak round
      cmd_reg = KMAC_CMD_REG_RESVAL;
      cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                       KMAC_CMD_CMD_VALUE_RUN);
      abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);

      // Let Keccak core finish the extra squeezing round
      HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));
    }
    digest->data[i] = abs_mmio_read8(kKmacBaseAddr + KMAC_STATE_REG_OFFSET +
                                     (i % keccak_rate));
    digest->data[i] ^=
        abs_mmio_read8(kKmacBaseAddr + KMAC_STATE_REG_OFFSET +
                       KMAC_STATE_SIZE_BYTES / 2 + (i % keccak_rate));
  }

  // Release the KMAC core, so that it goes back to idle mode
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_DONE);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);

  return OTCRYPTO_OK;
}

status_t kmac_sha3_224(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength224));

  return kmac_process_msg_blocks(kKmacOperationSHA3, message, digest);
}

status_t kmac_sha3_256(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength256));

  return kmac_process_msg_blocks(kKmacOperationSHA3, message, digest);
}

status_t kmac_sha3_384(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength384));

  return kmac_process_msg_blocks(kKmacOperationSHA3, message, digest);
}

status_t kmac_sha3_512(crypto_const_uint8_buf_t message,
                       crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength512));

  return kmac_process_msg_blocks(kKmacOperationSHA3, message, digest);
}

status_t kmac_shake_128(crypto_const_uint8_buf_t message,
                        crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHAKE, kKmacSecurityStrength128));

  return kmac_process_msg_blocks(kKmacOperationSHAKE, message, digest);
}

status_t kmac_shake_256(crypto_const_uint8_buf_t message,
                        crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHAKE, kKmacSecurityStrength256));

  return kmac_process_msg_blocks(kKmacOperationSHAKE, message, digest);
}

status_t kmac_cshake_128(crypto_const_uint8_buf_t message,
                         crypto_const_uint8_buf_t func_name,
                         crypto_const_uint8_buf_t cust_str,
                         crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationCSHAKE, kKmacSecurityStrength128));

  HARDENED_TRY(
      kmac_write_prefix_block(kKmacOperationCSHAKE, func_name, cust_str));

  return kmac_process_msg_blocks(kKmacOperationCSHAKE, message, digest);
}

status_t kmac_cshake_256(crypto_const_uint8_buf_t message,
                         crypto_const_uint8_buf_t func_name,
                         crypto_const_uint8_buf_t cust_str,
                         crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationCSHAKE, kKmacSecurityStrength256));

  HARDENED_TRY(
      kmac_write_prefix_block(kKmacOperationCSHAKE, func_name, cust_str));

  return kmac_process_msg_blocks(kKmacOperationCSHAKE, message, digest);
}

status_t kmac_kmac_128(kmac_blinded_key_t *key,
                       crypto_const_uint8_buf_t message,
                       crypto_const_uint8_buf_t cust_str,
                       crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationKMAC, kKmacSecurityStrength128));

  HARDENED_TRY(kmac_write_key_block(key));

  HARDENED_TRY(
      kmac_write_prefix_block(kKmacOperationKMAC, kKmacEmptyString, cust_str));

  return kmac_process_msg_blocks(kKmacOperationKMAC, message, digest);
}

status_t kmac_kmac_256(kmac_blinded_key_t *key,
                       crypto_const_uint8_buf_t message,
                       crypto_const_uint8_buf_t cust_str,
                       crypto_uint8_buf_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationKMAC, kKmacSecurityStrength256));

  HARDENED_TRY(kmac_write_key_block(key));

  HARDENED_TRY(
      kmac_write_prefix_block(kKmacOperationKMAC, kKmacEmptyString, cust_str));

  return kmac_process_msg_blocks(kKmacOperationKMAC, message, digest);
}
