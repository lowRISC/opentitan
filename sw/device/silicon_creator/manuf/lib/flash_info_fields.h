// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_

#include <stdint.h>

typedef struct flash_info_field {
  uint32_t partition;
  uint32_t bank;
  uint32_t page;
  uint32_t byte_offset;
} flash_info_field_t;

enum {
  // Creator/Owner Seeds - Bank 0, Pages 1 and 2
  kFlashInfoKeySeedSizeIn32BitWords = 256 / sizeof(uint32_t),

  // Wafer Authentication Secret - Bank 0, Page 3
  kFlashInfoWaferAuthSecretSizeIn32BitWords = 256 / sizeof(uint32_t),
};

extern const flash_info_field_t kFlashInfoFieldDeviceId;
extern const flash_info_field_t kFlashInfoFieldManufState;
extern const flash_info_field_t kFlashInfoFieldCreatorSeed;
extern const flash_info_field_t kFlashInfoFieldOwnerSeed;
extern const flash_info_field_t kFlashInfoFieldWaferAuthSecret;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
