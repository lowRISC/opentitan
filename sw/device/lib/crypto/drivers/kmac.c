// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'k', 'c')

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
  kKmacStateShareSize = KMAC_STATE_SIZE_BYTES / 2,
  kKmacStateShare0Addr = kKmacBaseAddr + KMAC_STATE_REG_OFFSET,
  kKmacStateShare1Addr =
      kKmacBaseAddr + KMAC_STATE_REG_OFFSET + kKmacStateShareSize,
};

// "KMAC" string in little endian
static const uint8_t kKmacFuncNameKMAC[] = {0x4b, 0x4d, 0x41, 0x43};

// We need 5 bytes at most for encoding the length of cust_str and func_name.
// That leaves 39 bytes for the string. We simply truncate it to 36 bytes.
OT_ASSERT_ENUM_VALUE(kKmacPrefixMaxSize, 4 * KMAC_PREFIX_MULTIREG_COUNT - 8);
OT_ASSERT_ENUM_VALUE(kKmacCustStrMaxSize, kKmacPrefixMaxSize - 4);

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
 * @param keccak_rate The keccak rate in 32-bit words.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_get_keccak_rate_words(kmac_security_str_t security_str,
                                           size_t *keccak_rate) {
  // Since Keccak state is 1600 bits, rate is calculated with
  // rate = (1600 - 2*x) where x is the security strength (i.e. half the
  // capacity).
  switch (security_str) {
    case kKmacSecurityStrength128:
      *keccak_rate = (1600 - 2 * 128) / 32;
      break;
    case kKmacSecurityStrength224:
      *keccak_rate = (1600 - 2 * 224) / 32;
      break;
    case kKmacSecurityStrength256:
      *keccak_rate = (1600 - 2 * 256) / 32;
      break;
    case kKmacSecurityStrength384:
      *keccak_rate = (1600 - 2 * 384) / 32;
      break;
    case kKmacSecurityStrength512:
      *keccak_rate = (1600 - 2 * 512) / 32;
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
  // Ensure that the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

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
 * The maximum `value` that can be encoded is restricted to the maximum value
 * that can be stored with `size_t` type.
 *
 * @param value Integer to be encoded.
 * @param[out] encoding_buf The output byte array representing `value`.
 * @param[out] encoding_header The number of bytes written to `encoded_value`.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t little_endian_encode(size_t value, uint8_t *encoding_buf,
                                     uint8_t *encoding_header) {
  uint8_t len = 0;
  uint8_t reverse_buf[sizeof(size_t)];
  do {
    reverse_buf[len] = value & UINT8_MAX;
    value >>= 8;
    len++;
  } while (value > 0);
  *encoding_header = len;

  for (size_t idx = 0; idx < len; idx++) {
    encoding_buf[idx] = reverse_buf[len - 1 - idx];
  }

  return OTCRYPTO_OK;
}

/**
 * Set prefix registers.
 *
 * This function directly writes to PREFIX registers of KMAC HWIP.
 * The combined size of customization string and the function name
 * must not exceed `kKmacPrefixMaxSize`.
 *
 * @param func_name Function name input in cSHAKE.
 * @param cust_str Customization string input in cSHAKE.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_set_prefix_regs(const unsigned char *func_name,
                                     size_t func_name_len,
                                     const unsigned char *cust_str,
                                     size_t cust_str_len) {
  // Initialize with 0 so that the last untouched bytes are set as 0x0
  uint32_t prefix_buffer[kKmacPrefixRegCount] = {0x0};
  unsigned char *prefix_buf_ptr = (unsigned char *)prefix_buffer;

  if (func_name_len + cust_str_len > kKmacPrefixMaxSize) {
    return OTCRYPTO_BAD_ARGS;
  }

  // left_encode(`func_name_len_bits`) below
  uint8_t bytes_written = 0;
  HARDENED_TRY(little_endian_encode(func_name_len << 3, prefix_buf_ptr + 1,
                                    &bytes_written));
  prefix_buf_ptr[0] = bytes_written;
  prefix_buf_ptr += bytes_written + 1;

  // copy `func_name`
  memcpy(prefix_buf_ptr, func_name, func_name_len);
  prefix_buf_ptr += func_name_len;

  // left_encode(`cust_str_len_bits`) below
  HARDENED_TRY(little_endian_encode(cust_str_len << 3, prefix_buf_ptr + 1,
                                    &bytes_written));
  prefix_buf_ptr[0] = bytes_written;
  prefix_buf_ptr += bytes_written + 1;

  // copy `cust_str`
  memcpy(prefix_buf_ptr, cust_str, cust_str_len);

  // Copy from `prefix_buffer` to PREFIX_REGS
  for (size_t i = 0; i < KMAC_PREFIX_MULTIREG_COUNT; i++) {
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
 * `hw_backed` must be either `kHardenedBoolFalse` or `kHardenedBoolTrue`. For
 * other values, this function returns an error.
 * For KMAC operations, if `hw_backed = kHardenedBoolTrue` the sideloaded key
 * coming from Keymgr is used. If `hw_backed = kHardenedBoolFalse`, the key
 * configured by SW is used.
 *
 * For non-KMAC operations, the value of `hw_backed` can be either of
 * `kHardenedBoolFalse` or `kHardenedBoolTrue`. It is recommended to set it to
 * `kHardenedBoolFalse` for consistency.
 *
 * @param operation The chosen operation, see kmac_operation_t struct.
 * @param security_str Security strength for KMAC (128 or 256).
 * @param hw_backed Whether the key comes from the sideload port.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_init(kmac_operation_t operation,
                          kmac_security_str_t security_str,
                          hardened_bool_t hw_backed) {
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));

  // If the operation is KMAC, ensure that the entropy complex has been
  // initialized for masking.
  if (operation == kKmacOperationKMAC) {
    HARDENED_TRY(entropy_complex_check());
  }

  // We need to preserve some bits of CFG register, such as:
  // entropy_mode, entropy_ready etc. On the other hand, some bits
  // need to be reset for each invocation.
  uint32_t cfg_reg =
      abs_mmio_read32(kKmacBaseAddr + KMAC_CFG_SHADOWED_REG_OFFSET);

  // Make sure kmac_en and sideload bits of CFG are reset at each invocation
  // These bits should be set to 1 only if needed by the rest of the code
  // in this function.
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_KMAC_EN_BIT, 0);
  if (hw_backed == kHardenedBoolTrue) {
    cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT, 1);
  } else if (hw_backed == kHardenedBoolFalse) {
    cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_SIDELOAD_BIT, 0);
  } else {
    return OTCRYPTO_BAD_ARGS;
  };

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
 * @param func_name_len Length of the function name in bytes.
 * @param cust_str The customization string (both for cSHAKE and KMAC).
 * @param cust_str_len Length of the customization string in bytes.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_write_prefix_block(kmac_operation_t operation,
                                        const unsigned char *func_name,
                                        size_t func_name_len,
                                        const unsigned char *cust_str,
                                        size_t cust_str_len) {
  if (operation == kKmacOperationCSHAKE) {
    return kmac_set_prefix_regs(func_name, func_name_len, cust_str,
                                cust_str_len);
  } else if (operation == kKmacOperationKMAC) {
    return kmac_set_prefix_regs(kKmacFuncNameKMAC, sizeof(kKmacFuncNameKMAC),
                                cust_str, cust_str_len);
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
 * streaming mode.
 *
 * This routine does not check input parameters for consistency. For instance,
 * one can invoke SHA-3_224 with digest_len=32, which will produce 256 bits of
 * digest. The caller is responsible for ensuring that the digest length and
 * mode are consistent.
 *
 * The caller must ensure that `message_len` bytes (rounded up to the next 32b
 * word) are allocated at the location pointed to by `message`, and similarly
 * that `digest_len_words` 32-bit words are allocated at the location pointed
 * to by `digest`.
 *
 * @param operation The operation type.
 * @param message Input message string.
 * @param message_len Message length in bytes.
 * @param digest The struct to which the result will be written.
 * @param digest_len_words Requested digest length in 32-bit words.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_process_msg_blocks(kmac_operation_t operation,
                                        const uint8_t *message,
                                        size_t message_len, uint32_t *digest,
                                        size_t digest_len_words) {
  // Block until KMAC is idle.
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));

  // Issue the start command, so that messages written to MSG_FIFO are forwarded
  // to Keccak
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_START);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_ABSORB_BIT, 1));

  // Begin by writing a one byte at a time until the data is aligned.
  size_t i = 0;
  for (; misalignment32_of((uintptr_t)(&message[i])) > 0 && i < message_len;
       i++) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    abs_mmio_write8(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET, message[i]);
  }

  // Write one word at a time as long as there is a full word available.
  for (; i + sizeof(uint32_t) <= message_len; i += sizeof(uint32_t)) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    uint32_t next_word = read_32(&message[i]);
    abs_mmio_write32(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET, next_word);
  }

  // For the last few bytes, we need to write one byte at a time again.
  for (; i < message_len; i++) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    abs_mmio_write8(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET, message[i]);
  }

  // If operation=KMAC, then we need to write `right_encode(digest->len)`
  if (operation == kKmacOperationKMAC) {
    uint32_t digest_len_bits = 8 * sizeof(uint32_t) * digest_len_words;
    if (digest_len_bits / (8 * sizeof(uint32_t)) != digest_len_words) {
      return OTCRYPTO_BAD_ARGS;
    }

    // right_encode(`digest_len_bit`) below
    // According to NIST SP 800-185, the maximum integer that can be encoded
    // with `right_encode` is the value represented with 255 bytes. However,
    // this driver supports only up to `digest_len_bits` that can be represented
    // with `size_t`.
    uint8_t buf[sizeof(size_t) + 1] = {0};
    uint8_t bytes_written;
    HARDENED_TRY(little_endian_encode(digest_len_bits, buf, &bytes_written));
    buf[bytes_written] = bytes_written;
    uint8_t *fifo_dst = (uint8_t *)(kKmacBaseAddr + KMAC_MSG_FIFO_REG_OFFSET);
    memcpy(fifo_dst, buf, bytes_written + 1);
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
  size_t keccak_rate_words;
  HARDENED_TRY(kmac_get_keccak_rate_words(keccak_str, &keccak_rate_words));

  // Finally, we can read the two shares of digest and XOR them.
  size_t idx = 0;

  while (launder32(idx) < digest_len_words) {
    // Since we always read in increments of the Keccak rate, the index at
    // start should always be a multiple of the rate.
    HARDENED_CHECK_EQ(idx % keccak_rate_words, 0);

    // Poll the status register until in the 'squeeze' state.
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

    // Read words from the state registers (either `digest_len_words` or the
    // maximum number of words available).
    size_t offset = 0;
    for (; launder32(idx) < digest_len_words && offset < keccak_rate_words;
         offset++) {
      uint32_t share0 =
          abs_mmio_read32(kKmacStateShare0Addr + offset * sizeof(uint32_t));
      uint32_t share1 =
          abs_mmio_read32(kKmacStateShare1Addr + offset * sizeof(uint32_t));
      digest[idx] = share0 ^ share1;
      ++idx;
    }

    // If we read all the remaining words and still need more digest, issue
    // `CMD.RUN` to generate more state.
    if (launder32(offset) == keccak_rate_words && idx < digest_len_words) {
      HARDENED_CHECK_EQ(offset, keccak_rate_words);
      cmd_reg = KMAC_CMD_REG_RESVAL;
      cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                       KMAC_CMD_CMD_VALUE_RUN);
      abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);
    }
  }
  HARDENED_CHECK_EQ(idx, digest_len_words);

  // Poll the status register until in the 'squeeze' state.
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

  // Release the KMAC core, so that it goes back to idle mode
  cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_DONE);
  abs_mmio_write32(kKmacBaseAddr + KMAC_CMD_REG_OFFSET, cmd_reg);

  return OTCRYPTO_OK;
}

status_t kmac_sha3_224(const uint8_t *message, size_t message_len,
                       uint32_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength224,
                         /*hw_backed=*/kHardenedBoolFalse));

  size_t digest_len_words = kSha3_224DigestWords;
  return kmac_process_msg_blocks(kKmacOperationSHA3, message, message_len,
                                 digest, digest_len_words);
}

status_t kmac_sha3_256(const uint8_t *message, size_t message_len,
                       uint32_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength256,
                         /*hw_backed=*/kHardenedBoolFalse));

  size_t digest_len_words = kSha3_256DigestWords;
  return kmac_process_msg_blocks(kKmacOperationSHA3, message, message_len,
                                 digest, digest_len_words);
}

status_t kmac_sha3_384(const uint8_t *message, size_t message_len,
                       uint32_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength384,
                         /*hw_backed=*/kHardenedBoolFalse));

  size_t digest_len_words = kSha3_384DigestWords;
  return kmac_process_msg_blocks(kKmacOperationSHA3, message, message_len,
                                 digest, digest_len_words);
}

status_t kmac_sha3_512(const uint8_t *message, size_t message_len,
                       uint32_t *digest) {
  HARDENED_TRY(kmac_init(kKmacOperationSHA3, kKmacSecurityStrength512,
                         /*hw_backed=*/kHardenedBoolFalse));

  size_t digest_len_words = kSha3_512DigestWords;
  return kmac_process_msg_blocks(kKmacOperationSHA3, message, message_len,
                                 digest, digest_len_words);
}

status_t kmac_shake_128(const uint8_t *message, size_t message_len,
                        uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(kmac_init(kKmacOperationSHAKE, kKmacSecurityStrength128,
                         /*hw_backed=*/kHardenedBoolFalse));

  return kmac_process_msg_blocks(kKmacOperationSHAKE, message, message_len,
                                 digest, digest_len);
}

status_t kmac_shake_256(const uint8_t *message, size_t message_len,
                        uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(kmac_init(kKmacOperationSHAKE, kKmacSecurityStrength256,
                         /*hw_backed=*/kHardenedBoolFalse));

  return kmac_process_msg_blocks(kKmacOperationSHAKE, message, message_len,
                                 digest, digest_len);
}

status_t kmac_cshake_128(const uint8_t *message, size_t message_len,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(kmac_init(kKmacOperationCSHAKE, kKmacSecurityStrength128,
                         /*hw_backed=*/kHardenedBoolFalse));

  HARDENED_TRY(kmac_write_prefix_block(kKmacOperationCSHAKE, func_name,
                                       func_name_len, cust_str, cust_str_len));

  return kmac_process_msg_blocks(kKmacOperationCSHAKE, message, message_len,
                                 digest, digest_len);
}

status_t kmac_cshake_256(const uint8_t *message, size_t message_len,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(kmac_init(kKmacOperationCSHAKE, kKmacSecurityStrength256,
                         /*hw_backed=*/kHardenedBoolFalse));

  HARDENED_TRY(kmac_write_prefix_block(kKmacOperationCSHAKE, func_name,
                                       func_name_len, cust_str, cust_str_len));

  return kmac_process_msg_blocks(kKmacOperationCSHAKE, message, message_len,
                                 digest, digest_len);
}

status_t kmac_kmac_128(kmac_blinded_key_t *key, const uint8_t *message,
                       size_t message_len, const unsigned char *cust_str,
                       size_t cust_str_len, uint32_t *digest,
                       size_t digest_len) {
  HARDENED_TRY(
      kmac_init(kKmacOperationKMAC, kKmacSecurityStrength128, key->hw_backed));

  if (key->hw_backed == kHardenedBoolTrue) {
    if (key->share0 != NULL || key->share1 != NULL ||
        key->len != kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
  } else if (key->hw_backed == kHardenedBoolFalse) {
    if (key->share0 == NULL || key->share1 == NULL) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(kmac_write_key_block(key));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(kmac_write_prefix_block(kKmacOperationKMAC, /*func_name=*/NULL,
                                       /*func_name_len=*/0, cust_str,
                                       cust_str_len));

  return kmac_process_msg_blocks(kKmacOperationKMAC, message, message_len,
                                 digest, digest_len);
}

status_t kmac_kmac_256(kmac_blinded_key_t *key, const uint8_t *message,
                       size_t message_len, const unsigned char *cust_str,
                       size_t cust_str_len, uint32_t *digest,
                       size_t digest_len) {
  HARDENED_TRY(
      kmac_init(kKmacOperationKMAC, kKmacSecurityStrength256, key->hw_backed));

  if (key->hw_backed == kHardenedBoolTrue) {
    if (key->share0 != NULL || key->share1 != NULL ||
        key->len != kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
  } else if (key->hw_backed == kHardenedBoolFalse) {
    if (key->share0 == NULL || key->share1 == NULL) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(kmac_write_key_block(key));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(kmac_write_prefix_block(kKmacOperationKMAC, /*func_name=*/NULL,
                                       /*func_name_len=*/0, cust_str,
                                       cust_str_len));

  return kmac_process_msg_blocks(kKmacOperationKMAC, message, message_len,
                                 digest, digest_len);
}
