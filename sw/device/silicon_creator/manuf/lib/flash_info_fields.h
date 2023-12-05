// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include "ast_regs.h"  // Generated.

typedef struct flash_info_field {
  uint32_t partition;
  uint32_t bank;
  uint32_t page;
  uint32_t byte_offset;
} flash_info_field_t;

enum {
  /**
   * AST Calibration Data Size - Bank 0, Page 0
   *
   * The format of data written to this field is:
   *
   * <# of address/data pairs><<address><data>>...<<address><data>>
   *
   * where each subfield (including the first length field) is a 32-bit word.
   */
  kFlashInfoFieldMaxAstCalibrationDataSizeInBytes =
      ((AST_REGAL_REG_OFFSET + 4) * 2) + 4,
  kFlashInfoFieldMaxAstCalibrationDataSizeIn32BitWords =
      kFlashInfoFieldMaxAstCalibrationDataSizeInBytes / sizeof(uint32_t),

  // Creator/Owner Seeds - Bank 0, Pages 1 and 2
  kFlashInfoKeySeedSizeIn32BitWords = 32 / sizeof(uint32_t),

  // Wafer Authentication Secret - Bank 0, Page 3
  kFlashInfoWaferAuthSecretSizeIn32BitWords = 32 / sizeof(uint32_t),
};

extern const flash_info_field_t kFlashInfoFieldDeviceId;
extern const flash_info_field_t kFlashInfoFieldManufState;
extern const flash_info_field_t kFlashInfoFieldAstCalibrationData;
extern const flash_info_field_t kFlashInfoFieldCreatorSeed;
extern const flash_info_field_t kFlashInfoFieldOwnerSeed;
extern const flash_info_field_t kFlashInfoFieldWaferAuthSecret;
extern const flash_info_field_t kFlashInfoFieldUdsAttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldCdi0AttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldCdi1AttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldUdsCertificate;
extern const flash_info_field_t kFlashInfoFieldCdi0Certificate;
extern const flash_info_field_t kFlashInfoFieldCdi1Certificate;

/**
 * Reads info flash page field.
 *
 * Assumes the page containing the field has already been configured for read
 * access.
 *
 * @param flash_state Flash controller instance.
 * @param field Flash info field information.
 * @param[out] data_out Output buffer.
 * @param num_words Number of words to read from flash and write to `data_out`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_flash_info_field_read(dif_flash_ctrl_state_t *flash_state,
                                     flash_info_field_t field, uint32_t *buf,
                                     size_t len);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
