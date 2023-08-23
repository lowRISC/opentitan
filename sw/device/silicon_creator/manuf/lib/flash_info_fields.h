// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_

#include "otp_ctrl_regs.h"  // Generated.

enum {
  /*****************************************************************************
   * Partition 0 pages and fields.
   * Refer to sw/device/silicon_creator/lib/drivers/flash_ctrl.h for what
   * information ROM and ROM_EXT expect to find on various pages.
   ****************************************************************************/
  // Device ID - Bank 0, Page 0
  kFlashInfoDeviceIdPartitionId = 0,
  kFlashInfoDeviceIdBankId = 0,
  kFlashInfoDeviceIdPageId = 0,
  kFlashInfoDeviceIdByteAddress = 0,

  // Manuf State - Bank 0, Page 0
  kFlashInfoManufStatePartitionId = 0,
  kFlashInfoManufStateBankId = 0,
  kFlashInfoManufStatePageId = 0,
  kFlashInfoManufStateByteAddress = OTP_CTRL_PARAM_DEVICE_ID_SIZE,

  // Creator Seed - Bank 0, Page 1
  kFlashInfoCreatorSeedPartitionId = 0,
  kFlashInfoCreatorSeedBankId = 0,
  kFlashInfoCreatorSeedPageId = 1,
  kFlashInfoCreatorSeedSizeInBytes = 32,
  kFlashInfoCreatorSeedSizeInWords =
      kFlashInfoCreatorSeedSizeInBytes / sizeof(uint32_t),

  // Owner Seed - Bank 0, Page 2
  kFlashInfoOwnerSeedPartitionId = 0,
  kFlashInfoOwnerSeedBankId = 0,
  kFlashInfoOwnerSeedPageId = 2,
  kFlashInfoOwnerSeedSizeInWords = kFlashInfoCreatorSeedSizeInWords,

  // Wafer Authentication Secret - Bank 0, Page 3
  kFlashInfoWaferAuthSecretPartitionId = 0,
  kFlashInfoWaferAuthSecretBankId = 0,
  kFlashInfoWaferAuthSecretPageId = 3,
};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
