// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_FIELDS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_FIELDS_H_

#include "sw/device/lib/base/bitfield.h"

#include "otp_ctrl_regs.h"  // Generated.

extern const bitfield_field32_t kSramFetch;
extern const bitfield_field32_t kCsrngAppRead;
extern const bitfield_field32_t kEntropySrcFwRd;
extern const bitfield_field32_t kEntropySrcFwOvr;

enum {
  /**
   * HW_CFG partition OTP fields.
   */
  // DEVICE_ID
  kHwCfgDeviceIdOffset =
      OTP_CTRL_PARAM_DEVICE_ID_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET,
  kHwCfgDeviceIdSizeInBytes = OTP_CTRL_PARAM_DEVICE_ID_SIZE,
  kHwCfgDeviceIdSizeIn32BitWords =
      OTP_CTRL_PARAM_DEVICE_ID_SIZE / sizeof(uint32_t),

  // MANUF_STATE
  kHwCfgManufStateOffset =
      OTP_CTRL_PARAM_MANUF_STATE_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET,
  kHwCfgManufStateSizeIn32BitWords =
      OTP_CTRL_PARAM_MANUF_STATE_SIZE / sizeof(uint32_t),

  // EN_SRAM_IFETCH
  kHwCfgEnSramIfetchOffset =
      OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET,

  /**
   * SECRET0 partition OTP fields.
   */
  kSecret0TestUnlockTokenOffset =
      OTP_CTRL_PARAM_TEST_UNLOCK_TOKEN_OFFSET - OTP_CTRL_PARAM_SECRET0_OFFSET,
  kSecret0TestUnlockTokenSizeInBytes = OTP_CTRL_PARAM_TEST_UNLOCK_TOKEN_SIZE,
  kSecret0TestUnlockTokenSizeIn32BitWords =
      kSecret0TestUnlockTokenSizeInBytes / sizeof(uint32_t),
  kSecret0TestUnlockTokenSizeIn64BitWords =
      kSecret0TestUnlockTokenSizeInBytes / sizeof(uint64_t),

  kSecret0TestExitTokenOffset =
      OTP_CTRL_PARAM_TEST_EXIT_TOKEN_OFFSET - OTP_CTRL_PARAM_SECRET0_OFFSET,
  kSecret0TestExitTokenSizeInBytes = OTP_CTRL_PARAM_TEST_EXIT_TOKEN_SIZE,
  kSecret0TestExitTokenSizeIn32BitWords =
      kSecret0TestExitTokenSizeInBytes / sizeof(uint32_t),
  kSecret0TestExitTokenSizeIn64BitWords =
      kSecret0TestExitTokenSizeInBytes / sizeof(uint64_t),

  /**
   * SECRET1 partition OTP fields.
   */
  kSecret1FlashAddrKeySeedOffset =
      OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_OFFSET - OTP_CTRL_PARAM_SECRET1_OFFSET,
  kSecret1FlashAddrKeySeed64BitWords =
      OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_SIZE / sizeof(uint64_t),

  kSecret1FlashDataKeySeedOffset =
      OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET - OTP_CTRL_PARAM_SECRET1_OFFSET,
  kSecret1FlashDataKeySeed64BitWords =
      OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_SIZE / sizeof(uint64_t),

  kSecret1SramDataKeySeedOffset =
      OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_OFFSET - OTP_CTRL_PARAM_SECRET1_OFFSET,
  kSecret1SramDataKeySeed64Bitwords =
      OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_SIZE / sizeof(uint64_t),

  /**
   * SECRET2 partition OTP fields.
   */
  // RMA_TOKEN
  kRmaUnlockTokenOffset =
      OTP_CTRL_PARAM_RMA_TOKEN_OFFSET - OTP_CTRL_PARAM_SECRET2_OFFSET,
  kRmaUnlockTokenSizeInBytes = OTP_CTRL_PARAM_RMA_TOKEN_SIZE,
  kRmaUnlockTokenSizeIn32BitWords =
      kRmaUnlockTokenSizeInBytes / sizeof(uint32_t),
  kRmaUnlockTokenSizeIn64BitWords =
      kRmaUnlockTokenSizeInBytes / sizeof(uint64_t),

  // CREATOR_ROOT_KEY
  kRootKeyShareSizeInBytes = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE,
  kRootKeyShareSizeIn32BitWords = kRootKeyShareSizeInBytes / sizeof(uint32_t),
  kRootKeyShareSizeIn64BitWords = kRootKeyShareSizeInBytes / sizeof(uint64_t),
  kRootKeyOffsetShare0 = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_OFFSET -
                         OTP_CTRL_PARAM_SECRET2_OFFSET,
  kRootKeyOffsetShare1 = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_OFFSET -
                         OTP_CTRL_PARAM_SECRET2_OFFSET,
};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_FIELDS_H_
