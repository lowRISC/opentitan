// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include "hw/top/ast_regs.h"  // Generated.

typedef struct flash_info_field {
  uint32_t partition;
  uint32_t bank;
  uint32_t page;
  uint32_t byte_offset;
} flash_info_field_t;

enum {
  /**
   * Lot Name Data Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldLotNameStartOffset = 80,
  kFlashInfoFieldLotNameSizeIn32BitWords = 1,

  /**
   * Wafer Number Data Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldWaferNumberStartOffset = 88,
  kFlashInfoFieldWaferNumberSizeIn32BitWords = 1,

  /**
   * Wafer X Coord Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldWaferXCoordStartOffset = 96,
  kFlashInfoFieldWaferXCoordSizeIn32BitWords = 1,

  /**
   * Wafer Y Coord Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldWaferYCoordStartOffset = 104,
  kFlashInfoFieldWaferYCoordSizeIn32BitWords = 1,

  /**
   * Process Data Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldProcessDataStartOffset = 112,
  kFlashInfoFieldProcessDataSizeIn32BitWords = 2,

  /**
   * AST Calibration Data Start / Size - Bank 0, Page 0
   *
   * Number of AST calibration words that will be stored in flash / OTP.
   */
  kFlashInfoFieldAstCalibrationDataStartOffset = 128,
  kFlashInfoAstCalibrationDataSizeInBytes =
      AST_REGAL_REG_OFFSET + sizeof(uint32_t),
  kFlashInfoAstCalibrationDataSizeIn32BitWords =
      kFlashInfoAstCalibrationDataSizeInBytes / sizeof(uint32_t),

  /**
   * CP Device ID Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldCpDeviceIdStartOffset = 384,
  kFlashInfoFieldCpDeviceIdSizeIn32BitWords = 4,
  kFlashInfoFieldCpDeviceIdSizeInBytes =
      kFlashInfoFieldCpDeviceIdSizeIn32BitWords * sizeof(uint32_t),

  /**
   * AST Individualize Patch Address Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldAstIndividPatchAddrStartOffset = 400,
  kFlashInfoFieldAstIndividPatchAddrSizeIn32BitWords = 1,

  /**
   * AST Individualize Patch Value Start / Size - Bank 0, Page 0
   */
  kFlashInfoFieldAstIndividPatchValStartOffset = 404,
  kFlashInfoFieldAstIndividPatchValSizeIn32BitWords = 1,

  // Creator/Owner Seeds - Bank 0, Pages 1 and 2
  kFlashInfoFieldKeySeedSizeIn32BitWords = 32 / sizeof(uint32_t),

  // Wafer Authentication Secret - Bank 0, Page 3
  kFlashInfoFieldWaferAuthSecretSizeIn32BitWords = 32 / sizeof(uint32_t),

  // Attestation key gen seed indices
  kFlashInfoFieldUdsKeySeedIdx = 0,
  kFlashInfoFieldCdi0KeySeedIdx = 1,
  kFlashInfoFieldCdi1KeySeedIdx = 2,
  kFlashInfoFieldTpmEkKeySeedIdx = 3,
};

// Info Page 0 fields.
extern const flash_info_field_t kFlashInfoFieldLotName;
extern const flash_info_field_t kFlashInfoFieldWaferNumber;
extern const flash_info_field_t kFlashInfoFieldWaferXCoord;
extern const flash_info_field_t kFlashInfoFieldWaferYCoord;
extern const flash_info_field_t kFlashInfoFieldProcessData;
extern const flash_info_field_t kFlashInfoFieldAstCalibrationData;
extern const flash_info_field_t kFlashInfoFieldCpDeviceId;
extern const flash_info_field_t kFlashInfoFieldAstIndividPatchAddr;
extern const flash_info_field_t kFlashInfoFieldAstIndividPatchVal;

// Info Page 1 fields.
extern const flash_info_field_t kFlashInfoFieldCreatorSeed;

// Info Page 2 fields.
extern const flash_info_field_t kFlashInfoFieldOwnerSeed;

// Info Page 3 fields.
extern const flash_info_field_t kFlashInfoFieldWaferAuthSecret;

// Info Page 4 fields.
extern const flash_info_field_t kFlashInfoFieldUdsAttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldCdi0AttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldCdi1AttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldTpmEkAttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldTpmCekAttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldTpmCikAttestationKeySeed;
extern const flash_info_field_t kFlashInfoFieldDevSeedSeed;
extern const flash_info_field_t kFlashInfoFieldAttestationKeyGenVersion;

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
                                     flash_info_field_t field,
                                     uint32_t *data_out, size_t num_words);

/**
 * Write info flash page field.
 *
 * Assumes the page containing the field has already been configured for
 * write/erase access.
 *
 * @param flash_state Flash controller instance.
 * @param field Flash info field information.
 * @param data_in Input buffer.
 * @param num_words Number of words to read from flash and write to `data_out`.
 * @param erase_page_before_write Whether to erase the page before writing it.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_flash_info_field_write(dif_flash_ctrl_state_t *flash_state,
                                      flash_info_field_t field,
                                      uint32_t *data_in, size_t num_words,
                                      bool erase_page_before_write);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_FLASH_INFO_FIELDS_H_
