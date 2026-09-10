// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "hw/top/dt/kmac.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"

#include "hw/top/kmac_regs.h"  // Generated.

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
  kKmacOperationSha3 = KMAC_CFG_SHADOWED_MODE_VALUE_SHA3 << 1 | 0,
  kKmacOperationShake = KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE << 1 | 0,
  kKmacOperationCshake = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE << 1 | 0,
  kKmacOperationKmac = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE << 1 | 1,
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
  kKmacStateShareSize = KMAC_STATE_SIZE_BYTES / 2,
};

// Inline wrapper function for KMAC base address
static inline uintptr_t kmac_base(void) {
  return dt_kmac_primary_reg_block(kDtKmac);
}

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
  kmac_security_str_t security_str_set = launder32(0);
  switch (launder32(security_str)) {
    case kKmacSecurityStrength128:
      *keccak_rate = (1600 - 2 * 128) / 32;
      security_str_set = launder32(security_str_set) | kKmacSecurityStrength128;
      break;
    case kKmacSecurityStrength224:
      *keccak_rate = (1600 - 2 * 224) / 32;
      security_str_set = launder32(security_str_set) | kKmacSecurityStrength224;
      break;
    case kKmacSecurityStrength256:
      *keccak_rate = (1600 - 2 * 256) / 32;
      security_str_set = launder32(security_str_set) | kKmacSecurityStrength256;
      break;
    case kKmacSecurityStrength384:
      *keccak_rate = (1600 - 2 * 384) / 32;
      security_str_set = launder32(security_str_set) | kKmacSecurityStrength384;
      break;
    case kKmacSecurityStrength512:
      *keccak_rate = (1600 - 2 * 512) / 32;
      security_str_set = launder32(security_str_set) | kKmacSecurityStrength512;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(security_str_set), security_str);
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
  size_t key_len_set = launder32(0);
  switch (launder32(key_len)) {
    case 128 / 8:
      *key_len_enum = kKmacKeyLength128;
      key_len_set = launder32(key_len_set) | (128 / 8);
      break;
    case 192 / 8:
      *key_len_enum = kKmacKeyLength192;
      key_len_set = launder32(key_len_set) | (192 / 8);
      break;
    case 256 / 8:
      *key_len_enum = kKmacKeyLength256;
      key_len_set = launder32(key_len_set) | (256 / 8);
      break;
    case 384 / 8:
      *key_len_enum = kKmacKeyLength384;
      key_len_set = launder32(key_len_set) | (384 / 8);
      break;
    case 512 / 8:
      *key_len_enum = kKmacKeyLength512;
      key_len_set = launder32(key_len_set) | (512 / 8);
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(key_len_set), key_len);
  return OTCRYPTO_OK;
}

status_t kmac_key_length_check(size_t key_len) {
  kmac_key_len_t key_len_enum;
  // Run the conversion to the key length enum, but we only care about the
  // error code.
  return kmac_get_key_len_bytes(key_len, &key_len_enum);
}

status_t kmac_hwip_default_configure(void) {
  uint32_t status_reg = abs_mmio_read32(kmac_base() + KMAC_STATUS_REG_OFFSET);

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
      abs_mmio_read32(kmac_base() + KMAC_INTR_STATE_REG_OFFSET);
  if (bitfield_bit32_read(intr_state, KMAC_INTR_STATE_KMAC_ERR_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  // Check CFG.regwen
  uint32_t cfg_regwen =
      abs_mmio_read32(kmac_base() + KMAC_CFG_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(cfg_regwen, KMAC_CFG_REGWEN_EN_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  // Keep err interrupt disabled
  uint32_t intr_reg = KMAC_INTR_ENABLE_REG_RESVAL;
  intr_reg = bitfield_bit32_write(intr_reg, KMAC_INTR_ENABLE_KMAC_ERR_BIT, 0);
  abs_mmio_write32(kmac_base() + KMAC_INTR_ENABLE_REG_OFFSET, intr_reg);

  // Configure max for entropy period (use UINT32_MAX and let bitfield clamp
  // them to their bitfield)
  uint32_t entropy_period = KMAC_ENTROPY_PERIOD_REG_RESVAL;
  entropy_period = bitfield_field32_write(
      entropy_period, KMAC_ENTROPY_PERIOD_PRESCALER_FIELD, UINT32_MAX);
  entropy_period = bitfield_field32_write(
      entropy_period, KMAC_ENTROPY_PERIOD_WAIT_TIMER_FIELD, UINT32_MAX);
  abs_mmio_write32(kmac_base() + KMAC_ENTROPY_PERIOD_REG_OFFSET,
                   entropy_period);

  // Configure max for hash threshold (use UINT32_MAX and let bitfield clamp
  // them to their bitfield)
  uint32_t entropy_hash_threshold =
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_RESVAL;
  entropy_hash_threshold = bitfield_field32_write(
      entropy_hash_threshold,
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_THRESHOLD_FIELD, UINT32_MAX);
  abs_mmio_write32_shadowed(
      kmac_base() + KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_OFFSET,
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
                                 KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT, 0);
  // Do not remask message blocks
  cfg_reg = bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_MSG_MASK_BIT, 0);

  // Mark entropy source as ready
  cfg_reg =
      bitfield_bit32_write(cfg_reg, KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, 1);
  // Unsupported modes: disabled
  cfg_reg = bitfield_bit32_write(
      cfg_reg, KMAC_CFG_SHADOWED_EN_UNSUPPORTED_MODESTRENGTH_BIT, 0);

  abs_mmio_write32_shadowed(kmac_base() + KMAC_CFG_SHADOWED_REG_OFFSET,
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
    uint32_t reg = abs_mmio_read32(kmac_base() + KMAC_STATUS_REG_OFFSET);
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

static void kmac_hwip_release(void) {
  // Do nothing when the block is already in `IDLE` mode.
  const uint32_t kBase = kmac_base();
  uint32_t status_reg = abs_mmio_read32(kBase + KMAC_STATUS_REG_OFFSET);
  if (bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_IDLE_BIT)) {
    return;
  }

  // If the hardware is still absorbing, terminate the absorption phase.
  if (bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_ABSORB_BIT)) {
    uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
    cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                     KMAC_CMD_CMD_VALUE_PROCESS);
    abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);
  }

  // Wait until the squeeze state is reached.
  if (!status_ok(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1))) {
    return;
  }

  // Issue `CMD.DONE` to wipe the internal state and release the hardware.
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_DONE);
  abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);
}

/**
 * Hardware wipe guard.
 *
 * Streaming operations disable the guard by setting it to `kHardenedBoolFalse`
 * when there is no error because the hardware must remain claimed between
 * calls.
 */
void kmac_wipe_guard(uint32_t *guard) {
  if (launder32(*guard) == kHardenedBoolFalse) {
    return;
  }
  kmac_hwip_release();
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

  return LAUNDERED_OTCRYPTO_OK;
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
    abs_mmio_write32(kmac_base() + prefix_offsets[i], prefix_buffer[i]);
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

  // We need to preserve some bits of CFG register, such as:
  // entropy_mode, entropy_ready etc. On the other hand, some bits
  // need to be reset for each invocation.
  uint32_t cfg_reg =
      abs_mmio_read32(kmac_base() + KMAC_CFG_SHADOWED_REG_OFFSET);

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
  abs_mmio_write32_shadowed(kmac_base() + KMAC_CFG_SHADOWED_REG_OFFSET,
                            cfg_reg);

  return OTCRYPTO_OK;
}

/**
 * Update the key registers with given key shares.
 *
 * The accepted `key->len` values are {128 / 8, 192 / 8, 256 / 8, 384 / 8,
 * 512 / 8}, otherwise an error will be returned.
 *
 * If the key is hardware-backed, this is a no-op.
 *
 * Uses hardening primitives internally that consume entropy; the caller must
 * ensure the entropy complex is up before calling.
 *
 * @param key The input key passed as a struct.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_write_key_block(kmac_blinded_key_t *key) {
  if (launder32(key->hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(key->hw_backed, kHardenedBoolTrue);
    // Nothing to do.
    return OTCRYPTO_OK;
  } else if (launder32(key->hw_backed) != kHardenedBoolFalse) {
    // Invalid value.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key->hw_backed, kHardenedBoolFalse);

  kmac_key_len_t key_len_enum;
  HARDENED_TRY(kmac_get_key_len_bytes(key->len, &key_len_enum));

  const uint32_t kBase = kmac_base();
  uint32_t key_len_reg = bitfield_field32_write(
      KMAC_KEY_LEN_REG_RESVAL, KMAC_KEY_LEN_LEN_FIELD, key_len_enum);
  abs_mmio_write32(kBase + KMAC_KEY_LEN_REG_OFFSET, key_len_reg);

  // Write random words to the key registers and use hardened_memcpy
  // for SCA defense. Using the hardened_mem* functions is fine as
  // we are always operating on multiples of 32-bit words.
  uint32_t share0_addr = kBase + KMAC_KEY_SHARE0_0_REG_OFFSET;
  uint32_t share1_addr = kBase + KMAC_KEY_SHARE1_0_REG_OFFSET;
  size_t key_len_words = key->len / sizeof(uint32_t);
  HARDENED_TRY(hardened_memshred((uint32_t *)share0_addr, key_len_words));
  HARDENED_TRY(
      hardened_memcpy((uint32_t *)share0_addr, key->share0, key_len_words));
  HARDENED_TRY(hardened_memshred((uint32_t *)share1_addr, key_len_words));
  HARDENED_TRY(
      hardened_memcpy((uint32_t *)share1_addr, key->share1, key_len_words));

  // Verify the checksum of the given key.
  HARDENED_CHECK_EQ(kmac_key_integrity_checksum_check(key), kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Issue the `START` command and wait until the absorb state is reached.
 *
 * Blocks until KMAC is idle before issuing the command. Afterwards this
 * function returns successfully.
 *
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_msg_start(void) {
  // Block until KMAC is idle.
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));

  // Issue the start command, so that messages written to MSG_FIFO are forwarded
  // to Keccak
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_START);
  abs_mmio_write32(kmac_base() + KMAC_CMD_REG_OFFSET, cmd_reg);
  return wait_status_bit(KMAC_STATUS_SHA3_ABSORB_BIT, 1);
}

/**
 * Write given message bytes to the message FIFO.
 *
 * The KMAC HWIP must be in the absorb state, i.e. `kmac_msg_start` must have
 * been called beforehand. This function may be called multiple times to feed
 * a message in several steps.
 *
 * @param message Input message string.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_msg_fifo_write(const otcrypto_const_byte_buf_t *message) {
  const uint32_t kBase = kmac_base();

  // Begin by writing a one byte at a time until the data is aligned.
  size_t i = 0;
  for (; misalignment32_of((uintptr_t)(&message->data[i])) > 0 &&
         i < message->len;
       i++) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    abs_mmio_write8(kBase + KMAC_MSG_FIFO_REG_OFFSET, message->data[i]);
  }

  // Write one word at a time as long as there is a full word available.
  for (; i + sizeof(uint32_t) <= message->len; i += sizeof(uint32_t)) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    uint32_t next_word = read_32(&message->data[i]);
    abs_mmio_write32(kBase + KMAC_MSG_FIFO_REG_OFFSET, next_word);
  }
  // Check that the loops ran for the correct number of iterations.
  HARDENED_CHECK_LT(message->len, i + sizeof(uint32_t));

  // For the last few bytes, we need to write one byte at a time again.
  for (; i < message->len; i++) {
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_FIFO_FULL_BIT, 0));
    abs_mmio_write8(kBase + KMAC_MSG_FIFO_REG_OFFSET, message->data[i]);
  }
  // Check that the loops ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, message->len);

  // Verify the input buffer
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(message));

  return OTCRYPTO_OK;
}

/**
 * Finish the absorb phase and squeeze the digest out of the KMAC HWIP.
 *
 * All message bytes must already have been absorbed through the function
 * `kmac_msg_fifo_write`. For KMAC operations, this function appends
 * `right_encode(digest_len)` to the message before issuing the `PROCESS`
 * command.
 *
 * This routine does not check input parameters for consistency. For instance,
 * one can invoke SHA-3_224 with digest_len=32, which will produce 256 bits of
 * digest. The caller is responsible for ensuring that the digest length and
 * mode are consistent.
 *
 * If `masked_digest` is set, then `digest` must be twice as large in order to
 * fit both shares.
 *
 * The caller is responsible for issuing the DONE command after reading the
 * digest (e.g. by means of `kmac_wipe_guard`).
 *
 * @param operation The operation type.
 * @param digest The digest location to which the result will be written.
 * @param digest_len_bytes Requested digest length in bytes.
 * @param masked_digest Whether to return the digest in two shares.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_squeeze(kmac_operation_t operation, uint32_t *digest,
                             size_t digest_len_bytes,
                             hardened_bool_t masked_digest) {
  const uint32_t kBase = kmac_base();
  size_t digest_len_words =
      (digest_len_bytes + sizeof(uint32_t) - 1) / sizeof(uint32_t);

  // If the operation is KMAC, then `right_encode(digest->len)` is appended.
  if (operation == kKmacOperationKmac) {
    uint32_t digest_len_bits = 8 * digest_len_bytes;
    // Check for overflow, i.e., when the input buffer is too large.
    if (digest_len_bits / 8 != digest_len_bytes) {
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
    uint8_t *fifo_dst = (uint8_t *)(kBase + KMAC_MSG_FIFO_REG_OFFSET);
    memcpy(fifo_dst, buf, bytes_written + 1);
  }

  // Issue the process command, so that squeezing phase can start
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_PROCESS);
  abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);

  // Wait until squeezing is done
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

  uint32_t cfg_reg = abs_mmio_read32(kBase + KMAC_CFG_SHADOWED_REG_OFFSET);
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
    uint32_t offset_share0 = kBase + KMAC_STATE_REG_OFFSET;
    uint32_t offset_share1 =
        kBase + KMAC_STATE_REG_OFFSET + kKmacStateShareSize;
    size_t read_len_words = keccak_rate_words;
    if (idx + read_len_words >= digest_len_words) {
      read_len_words = digest_len_words - idx;
    }
    if (launder32(masked_digest) == kHardenedBoolTrue) {
      HARDENED_CHECK_EQ(masked_digest, kHardenedBoolTrue);
      // Read the digest into each share in turn. Do this by using the SCA
      // resilient hardened_memcpy function.
      HARDENED_TRY(hardened_memcpy(
          &digest[idx], (const uint32_t *)offset_share0, read_len_words));
      HARDENED_TRY(hardened_memcpy(&digest[idx + digest_len_words],
                                   (const uint32_t *)offset_share1,
                                   read_len_words));
    } else {
      // Skip right to the hardened check here instead of returning
      // `OTCRYPTO_BAD_ARGS` if the value is not `kHardenedBoolFalse`; this
      // value always comes from within the cryptolib, so we expect it to be
      // valid and should be suspicious if it's not.
      HARDENED_CHECK_EQ(masked_digest, kHardenedBoolFalse);
      // Unmask the digest as we read it.
      HARDENED_TRY(hardened_xor((const uint32_t *)offset_share0,
                                (const uint32_t *)offset_share1, read_len_words,
                                &digest[idx]));
    }
    offset += read_len_words;
    idx += read_len_words;

    // If we read all the remaining words and still need more digest, issue
    // `CMD.RUN` to generate more state.
    if (launder32(offset) == keccak_rate_words && idx < digest_len_words) {
      HARDENED_CHECK_EQ(offset, keccak_rate_words);
      cmd_reg = KMAC_CMD_REG_RESVAL;
      cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                       KMAC_CMD_CMD_VALUE_RUN);
      abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);
    }
  }
  HARDENED_CHECK_EQ(idx, digest_len_words);

  // Poll the status register until in the 'squeeze' state.
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

  // Zero out the trailing bytes in the final word.
  size_t remainder_bytes = digest_len_bytes % sizeof(uint32_t);
  if (remainder_bytes > 0) {
    uint32_t mask = (1U << (remainder_bytes * 8)) - 1;
    digest[digest_len_words - 1] &= mask;
    if (launder32(masked_digest) == kHardenedBoolTrue) {
      digest[2 * digest_len_words - 1] &= mask;
    }
  }

  return OTCRYPTO_OK;
}

/**
 * Common function for processing message blocks.
 *
 * Before running this, the operation type must be configured with `kmac_init`.
 * Then, we can use this function to absorb various bytes of data.
 * This is a one-shot implementation, and it does not support streaming mode.
 *
 * This routine does not check input parameters for consistency.
 *
 * If `masked_digest` is set, then `digest` must contain twice the amount of
 * `digest_len_words` to fit both shares.
 *
 * @param operation The operation type.
 * @param message Input message string.
 * @param digest The digest location to which the result will be written.
 * @param digest_len_bytes Requested digest length in bytes.
 * @param masked_digest Whether to return the digest in two shares.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t kmac_process_msg_blocks(
    kmac_operation_t operation, const otcrypto_const_byte_buf_t *message,
    uint32_t *digest, size_t digest_len_bytes, hardened_bool_t masked_digest) {
  // This variable guarantees kmac_wipe_guard() is called on exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  HARDENED_TRY(kmac_msg_start());
  HARDENED_TRY(kmac_msg_fifo_write(message));
  return kmac_squeeze(operation, digest, digest_len_bytes, masked_digest);
}

/**
 * Perform a one-shot SHA3, SHAKE, or cSHAKE operation.
 *
 * Do not use this routine for KMAC operations.
 *
 * @param operation Hash function to perform.
 * @param strength Security strength parameter.
 * @param message Message data to hash.
 * @param message_len Length of message data in bytes.
 * @param digest_wordlen Length of digest in words.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t hash(kmac_operation_t operation, kmac_security_str_t strength,
                     const otcrypto_const_byte_buf_t *message,
                     size_t digest_wordlen, uint32_t *digest) {
  // Note: to save code size, we check for null pointers here instead of
  // separately for every different Keccak hash operation.
  if (digest == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(kmac_init(operation, strength,
                         /*hw_backed=*/kHardenedBoolFalse));

  return kmac_process_msg_blocks(operation, message, digest,
                                 digest_wordlen * sizeof(uint32_t),
                                 /*masked_digest=*/kHardenedBoolFalse);
}

inline status_t kmac_sha3_224(const otcrypto_const_byte_buf_t *message,
                              uint32_t *digest) {
  return hash(kKmacOperationSha3, kKmacSecurityStrength224, message,
              kKmacSha3224DigestWords, digest);
}

inline status_t kmac_sha3_256(const otcrypto_const_byte_buf_t *message,
                              uint32_t *digest) {
  return hash(kKmacOperationSha3, kKmacSecurityStrength256, message,
              kKmacSha3256DigestWords, digest);
}

inline status_t kmac_sha3_384(const otcrypto_const_byte_buf_t *message,
                              uint32_t *digest) {
  return hash(kKmacOperationSha3, kKmacSecurityStrength384, message,
              kKmacSha3384DigestWords, digest);
}

inline status_t kmac_sha3_512(const otcrypto_const_byte_buf_t *message,
                              uint32_t *digest) {
  return hash(kKmacOperationSha3, kKmacSecurityStrength512, message,
              kKmacSha3512DigestWords, digest);
}

inline status_t kmac_shake_128(const otcrypto_const_byte_buf_t *message,
                               uint32_t *digest, size_t digest_len) {
  return hash(kKmacOperationShake, kKmacSecurityStrength128, message,
              digest_len, digest);
}

inline status_t kmac_shake_256(const otcrypto_const_byte_buf_t *message,
                               uint32_t *digest, size_t digest_len) {
  return hash(kKmacOperationShake, kKmacSecurityStrength256, message,
              digest_len, digest);
}

status_t kmac_cshake_128(const otcrypto_const_byte_buf_t *message,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));
  HARDENED_TRY(
      kmac_set_prefix_regs(func_name, func_name_len, cust_str, cust_str_len));
  return hash(kKmacOperationCshake, kKmacSecurityStrength128, message,
              digest_len, digest);
}

status_t kmac_cshake_256(const otcrypto_const_byte_buf_t *message,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));
  HARDENED_TRY(
      kmac_set_prefix_regs(func_name, func_name_len, cust_str, cust_str_len));
  return hash(kKmacOperationCshake, kKmacSecurityStrength256, message,
              digest_len, digest);
}

status_t kmac_kmac_128(kmac_blinded_key_t *key, hardened_bool_t masked_digest,
                       const otcrypto_const_byte_buf_t *message,
                       const unsigned char *cust_str, size_t cust_str_len,
                       uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(
      kmac_init(kKmacOperationKmac, kKmacSecurityStrength128, key->hw_backed));

  HARDENED_TRY(kmac_write_key_block(key));
  // "KMAC" string in little endian
  const uint8_t kKmacFuncNameKMAC[] = {0x4b, 0x4d, 0x41, 0x43};
  HARDENED_TRY(kmac_set_prefix_regs(
      kKmacFuncNameKMAC, sizeof(kKmacFuncNameKMAC), cust_str, cust_str_len));

  return kmac_process_msg_blocks(kKmacOperationKmac, message, digest,
                                 digest_len, masked_digest);
}

status_t kmac_kmac_256(kmac_blinded_key_t *key, hardened_bool_t masked_digest,
                       const otcrypto_const_byte_buf_t *message,
                       const unsigned char *cust_str, size_t cust_str_len,
                       uint32_t *digest, size_t digest_len) {
  HARDENED_TRY(
      kmac_init(kKmacOperationKmac, kKmacSecurityStrength256, key->hw_backed));

  HARDENED_TRY(kmac_write_key_block(key));
  // "KMAC" string in little endian
  const uint8_t kKmacFuncNameKMAC[] = {0x4b, 0x4d, 0x41, 0x43};
  HARDENED_TRY(kmac_set_prefix_regs(
      kKmacFuncNameKMAC, sizeof(kKmacFuncNameKMAC), cust_str, cust_str_len));

  return kmac_process_msg_blocks(kKmacOperationKmac, message, digest,
                                 digest_len, masked_digest);
}

/**
 * Start a streamed operation.
 *
 * Configures the KMAC HWIP for the given operation and issues the `START`
 * command, leaving the hardware in the `ABSORB` state. The hardware remains
 * claimed by this streaming operation until the corresponding `final()`.
 *
 * @param operation The chosen operation, see kmac_operation_t struct.
 * @param security_str Security strength.
 * @param hw_backed Whether the key comes from the sideload port.
 * @param[out] ctx KMAC context.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t stream_init(kmac_operation_t operation,
                            kmac_security_str_t security_str,
                            hardened_bool_t hw_backed, kmac_ctx_t *ctx) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  ctx->operation = operation;
  ctx->security_str = security_str;
  ctx->squeeze_started = kHardenedBoolFalse;
  ctx->squeeze_offset = 0;

  // This variable guarantees kmac_wipe_guard() is called on exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  HARDENED_TRY(kmac_init(operation, security_str, hw_backed));
  HARDENED_TRY(kmac_msg_start());

  // Disable the guard.
  hw_cleanup_guard = kHardenedBoolFalse;

  return OTCRYPTO_OK;
}

/**
 * Finalize a streamed operation.
 *
 * Ends the absorption phase and squeezes the requested number of digest bytes
 * out of the KMAC HWIP. The hardware must still be in the `ABSORB` state.
 *
 * @param ctx KMAC context.
 * @param operation The expected operation for this context.
 * @param security_str The expected security strength for this context.
 * @param masked_digest Whether to return the digest in two shares.
 * @param[out] digest Output buffer for the result.
 * @param digest_len_bytes Requested digest length in bytes.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t stream_final(kmac_ctx_t *ctx, kmac_operation_t operation,
                             kmac_security_str_t security_str,
                             hardened_bool_t masked_digest, uint32_t *digest,
                             size_t digest_len_bytes) {
  // This variable guarantees kmac_wipe_guard() is called on exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  if (ctx == NULL || digest == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the hardware is still in the `ABSORB` state.
  uint32_t status_reg = abs_mmio_read32(kmac_base() + KMAC_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_ABSORB_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  HARDENED_TRY(
      kmac_squeeze(operation, digest, digest_len_bytes, masked_digest));

  return OTCRYPTO_OK;
}

/**
 * Start a streamed KMAC operation.
 *
 * Common helper function for `kmac_kmac_{128,256}_init`. Configures the key
 * and the prefix registers before starting the absorption phase.
 *
 * @param security_str Security strength (128 or 256).
 * @param key The KMAC key.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] ctx KMAC context.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t stream_kmac_init(kmac_security_str_t security_str,
                                 kmac_blinded_key_t *key,
                                 const unsigned char *cust_str,
                                 size_t cust_str_len, kmac_ctx_t *ctx) {
  if (ctx == NULL || key == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  ctx->operation = kKmacOperationKmac;
  ctx->security_str = security_str;
  ctx->squeeze_started = kHardenedBoolFalse;
  ctx->squeeze_offset = 0;

  // Release the hardware through kmac_wipe_guard() on any error exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  HARDENED_TRY(kmac_init(kKmacOperationKmac, security_str, key->hw_backed));

  HARDENED_TRY(kmac_write_key_block(key));
  // "KMAC" string in little endian
  const uint8_t kKmacFuncNameKMAC[] = {0x4b, 0x4d, 0x41, 0x43};
  HARDENED_TRY(kmac_set_prefix_regs(
      kKmacFuncNameKMAC, sizeof(kKmacFuncNameKMAC), cust_str, cust_str_len));

  HARDENED_TRY(kmac_msg_start());

  // Disarm the guard: the hardware remains claimed by this streaming
  // operation until the corresponding `final()`.
  hw_cleanup_guard = kHardenedBoolFalse;
  return OTCRYPTO_OK;
}

status_t kmac_sha3_224_init(kmac_ctx_t *ctx) {
  return stream_init(kKmacOperationSha3, kKmacSecurityStrength224,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_sha3_256_init(kmac_ctx_t *ctx) {
  return stream_init(kKmacOperationSha3, kKmacSecurityStrength256,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_sha3_384_init(kmac_ctx_t *ctx) {
  return stream_init(kKmacOperationSha3, kKmacSecurityStrength384,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_sha3_512_init(kmac_ctx_t *ctx) {
  return stream_init(kKmacOperationSha3, kKmacSecurityStrength512,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_shake_128_init(kmac_ctx_t *ctx) {
  return stream_init(kKmacOperationShake, kKmacSecurityStrength128,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_shake_256_init(kmac_ctx_t *ctx) {
  return stream_init(kKmacOperationShake, kKmacSecurityStrength256,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_cshake_128_init(const unsigned char *func_name,
                              size_t func_name_len,
                              const unsigned char *cust_str,
                              size_t cust_str_len, kmac_ctx_t *ctx) {
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));
  HARDENED_TRY(
      kmac_set_prefix_regs(func_name, func_name_len, cust_str, cust_str_len));
  return stream_init(kKmacOperationCshake, kKmacSecurityStrength128,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_cshake_256_init(const unsigned char *func_name,
                              size_t func_name_len,
                              const unsigned char *cust_str,
                              size_t cust_str_len, kmac_ctx_t *ctx) {
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_IDLE_BIT, 1));
  HARDENED_TRY(
      kmac_set_prefix_regs(func_name, func_name_len, cust_str, cust_str_len));
  return stream_init(kKmacOperationCshake, kKmacSecurityStrength256,
                     /*hw_backed=*/kHardenedBoolFalse, ctx);
}

status_t kmac_kmac_128_init(kmac_blinded_key_t *key,
                            const unsigned char *cust_str, size_t cust_str_len,
                            kmac_ctx_t *ctx) {
  return stream_kmac_init(kKmacSecurityStrength128, key, cust_str, cust_str_len,
                          ctx);
}

status_t kmac_kmac_256_init(kmac_blinded_key_t *key,
                            const unsigned char *cust_str, size_t cust_str_len,
                            kmac_ctx_t *ctx) {
  return stream_kmac_init(kKmacSecurityStrength256, key, cust_str, cust_str_len,
                          ctx);
}

status_t kmac_update(kmac_ctx_t *ctx, const otcrypto_const_byte_buf_t *data) {
  // Release the hardware through kmac_wipe_guard() on any error exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  if (ctx == NULL || data == NULL || (data->data == NULL && data->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the hardware is still in the `ABSORB` state.
  uint32_t status_reg = abs_mmio_read32(kmac_base() + KMAC_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_ABSORB_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  HARDENED_TRY(kmac_msg_fifo_write(data));

  // Disarm the guard.
  hw_cleanup_guard = kHardenedBoolFalse;

  return OTCRYPTO_OK;
}

/**
 * End the absorption phase and transition to processing.
 *
 * @param ctx KMAC context.
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
static status_t xof_process(kmac_ctx_t *ctx) {
  const uint32_t kBase = kmac_base();

  // Check that the hardware is still in the `ABSORB` state.
  uint32_t status_reg = abs_mmio_read32(kBase + KMAC_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(status_reg, KMAC_STATUS_SHA3_ABSORB_BIT)) {
    return OTCRYPTO_RECOV_ERR;
  }

  // Issue `CMD.PROCESS`, so that the squeezing phase can start.
  uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
  cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                   KMAC_CMD_CMD_VALUE_PROCESS);
  abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);

  ctx->squeeze_started = kHardenedBoolTrue;
  ctx->squeeze_offset = 0;

  return OTCRYPTO_OK;
}

status_t kmac_xof_squeeze(kmac_ctx_t *ctx, uint32_t *digest,
                          size_t digest_len) {
  // Release the hardware through kmac_wipe_guard() on any error exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  if (ctx == NULL || digest == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Only SHAKE and cSHAKE support streamed squeezing.
  if (launder32(ctx->operation) != kKmacOperationShake &&
      launder32(ctx->operation) != kKmacOperationCshake) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t keccak_rate_words;
  HARDENED_TRY(
      kmac_get_keccak_rate_words(ctx->security_str, &keccak_rate_words));

  // The squeeze offset must be at most the size of the rate.
  if (launder32(ctx->squeeze_offset) > keccak_rate_words) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(ctx->squeeze_offset, keccak_rate_words);

  const uint32_t kBase = kmac_base();

  // The first invocation ends the absorb phase.
  if (launder32(ctx->squeeze_started) != kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(ctx->squeeze_started, kHardenedBoolFalse);
    HARDENED_TRY(xof_process(ctx));
  }

  size_t idx = 0;
  while (launder32(idx) < digest_len) {
    // Poll the status register until in the 'SQUEEZE' state.
    HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

    // If we read all the remaining words and still need more digest, issue
    // `CMD.RUN` to generate more state.
    if (launder32(ctx->squeeze_offset) == keccak_rate_words) {
      HARDENED_CHECK_EQ(ctx->squeeze_offset, keccak_rate_words);
      uint32_t cmd_reg = KMAC_CMD_REG_RESVAL;
      cmd_reg = bitfield_field32_write(cmd_reg, KMAC_CMD_CMD_FIELD,
                                       KMAC_CMD_CMD_VALUE_RUN);
      abs_mmio_write32(kBase + KMAC_CMD_REG_OFFSET, cmd_reg);
      ctx->squeeze_offset = 0;
      HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));
    }

    // Read words from the state registers.
    size_t read_len_words = keccak_rate_words - ctx->squeeze_offset;
    if (read_len_words > digest_len - idx) {
      read_len_words = digest_len - idx;
    }
    uint32_t offset_share0 =
        kBase + KMAC_STATE_REG_OFFSET + ctx->squeeze_offset * sizeof(uint32_t);
    uint32_t offset_share1 = offset_share0 + kKmacStateShareSize;

    // Unmask the digest as we read it.
    HARDENED_TRY(hardened_xor((const uint32_t *)offset_share0,
                              (const uint32_t *)offset_share1, read_len_words,
                              &digest[idx]));
    idx += read_len_words;
    ctx->squeeze_offset += read_len_words;
  }
  HARDENED_CHECK_EQ(idx, digest_len);

  // Disarm the guard.
  hw_cleanup_guard = kHardenedBoolFalse;

  return OTCRYPTO_OK;
}

status_t kmac_xof_end(kmac_ctx_t *ctx) {
  // Release the hardware through kmac_wipe_guard() on any error exit.
  uint32_t hw_cleanup_guard __attribute__((cleanup(kmac_wipe_guard))) =
      kHardenedBoolTrue;
  barrier32(hw_cleanup_guard);

  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // If squeezing has not started, end the absorb phase first so that the
  // hardware reaches a state in which it accepts the `CMD.DONE` command.
  if (launder32(ctx->squeeze_started) != kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(ctx->squeeze_started, kHardenedBoolFalse);
    HARDENED_TRY(xof_process(ctx));
  }
  HARDENED_TRY(wait_status_bit(KMAC_STATUS_SHA3_SQUEEZE_BIT, 1));

  // Invalidate the context.
  ctx->squeeze_started = kHardenedBoolFalse;
  ctx->squeeze_offset = 0;

  return OTCRYPTO_OK;
}

status_t kmac_sha3_224_final(kmac_ctx_t *ctx, uint32_t *digest) {
  return stream_final(ctx, kKmacOperationSha3, kKmacSecurityStrength224,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      kKmacSha3224DigestBytes);
}

status_t kmac_sha3_256_final(kmac_ctx_t *ctx, uint32_t *digest) {
  return stream_final(ctx, kKmacOperationSha3, kKmacSecurityStrength256,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      kKmacSha3256DigestBytes);
}

status_t kmac_sha3_384_final(kmac_ctx_t *ctx, uint32_t *digest) {
  return stream_final(ctx, kKmacOperationSha3, kKmacSecurityStrength384,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      kKmacSha3384DigestBytes);
}

status_t kmac_sha3_512_final(kmac_ctx_t *ctx, uint32_t *digest) {
  return stream_final(ctx, kKmacOperationSha3, kKmacSecurityStrength512,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      kKmacSha3512DigestBytes);
}

status_t kmac_shake_128_final(kmac_ctx_t *ctx, uint32_t *digest,
                              size_t digest_len) {
  return stream_final(ctx, kKmacOperationShake, kKmacSecurityStrength128,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      digest_len * sizeof(uint32_t));
}

status_t kmac_shake_256_final(kmac_ctx_t *ctx, uint32_t *digest,
                              size_t digest_len) {
  return stream_final(ctx, kKmacOperationShake, kKmacSecurityStrength256,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      digest_len * sizeof(uint32_t));
}

status_t kmac_cshake_128_final(kmac_ctx_t *ctx, uint32_t *digest,
                               size_t digest_len) {
  return stream_final(ctx, kKmacOperationCshake, kKmacSecurityStrength128,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      digest_len * sizeof(uint32_t));
}

status_t kmac_cshake_256_final(kmac_ctx_t *ctx, uint32_t *digest,
                               size_t digest_len) {
  return stream_final(ctx, kKmacOperationCshake, kKmacSecurityStrength256,
                      /*masked_digest=*/kHardenedBoolFalse, digest,
                      digest_len * sizeof(uint32_t));
}

status_t kmac_kmac_128_final(kmac_ctx_t *ctx, hardened_bool_t masked_digest,
                             uint32_t *digest, size_t digest_len) {
  return stream_final(ctx, kKmacOperationKmac, kKmacSecurityStrength128,
                      masked_digest, digest, digest_len);
}

status_t kmac_kmac_256_final(kmac_ctx_t *ctx, hardened_bool_t masked_digest,
                             uint32_t *digest, size_t digest_len) {
  return stream_final(ctx, kKmacOperationKmac, kKmacSecurityStrength256,
                      masked_digest, digest, digest_len);
}

uint32_t kmac_key_integrity_checksum(const kmac_blinded_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  crc32_add32(&ctx, key->len);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)key->share0, key->len);
  crc32_add32(&ctx, key->hw_backed);
  return crc32_finish(&ctx);
}

hardened_bool_t kmac_key_integrity_checksum_check(
    const kmac_blinded_key_t *key) {
  if (key->checksum == launder32(kmac_key_integrity_checksum(key))) {
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
