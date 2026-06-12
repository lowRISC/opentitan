// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_NVM_INFO_FIELD_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_NVM_INFO_FIELD_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/nvm_testutils.h"

#include "hw/top/ast_regs.h"  // Generated.

/**
 * An NVM info field: a named region within a logical info page.
 *
 * `page` identifies the page and `byte_offset` is the byte offset from the
 * start of that page.  All physical details (bank, partition) are resolved
 * internally by the nvm_testutils layer.
 */
typedef struct nvm_info_field {
  nvm_info_page_t page;
  uint32_t byte_offset;
} nvm_info_field_t;

enum {
  /**
   * Lot Name Data Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldLotNameStartOffset = 80,
  kNvmInfoFieldLotNameSizeIn32BitWords = 1,

  /**
   * Wafer Number Data Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldWaferNumberStartOffset = 88,
  kNvmInfoFieldWaferNumberSizeIn32BitWords = 1,

  /**
   * Wafer X Coord Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldWaferXCoordStartOffset = 96,
  kNvmInfoFieldWaferXCoordSizeIn32BitWords = 1,

  /**
   * Wafer Y Coord Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldWaferYCoordStartOffset = 104,
  kNvmInfoFieldWaferYCoordSizeIn32BitWords = 1,

  /**
   * Process Data Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldProcessDataStartOffset = 112,
  kNvmInfoFieldProcessDataSizeIn32BitWords = 2,

  /**
   * AST Calibration Data Start / Size - Bank 0, Page 0
   *
   * Number of AST calibration words that will be stored in NVM / OTP.
   */
  kNvmInfoFieldAstCalibrationDataStartOffset = 128,
  kNvmInfoAstCalibrationDataSizeInBytes =
      AST_REGAL_REG_OFFSET + sizeof(uint32_t),
  kNvmInfoAstCalibrationDataSizeIn32BitWords =
      kNvmInfoAstCalibrationDataSizeInBytes / sizeof(uint32_t),

  /**
   * AST Calibration Version Start / Size - Bank 0, Page 0
   *
   * The version of the AST calibration words that are stored in NVM / OTP.
   */
  kNvmInfoFieldAstCfgVersionStartOffset = 368,
  kNvmInfoFieldAstCfgVersionSizeIn32BitWords = 1,

  /**
   * CP Device ID Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldCpDeviceIdStartOffset = 384,
  kNvmInfoFieldCpDeviceIdSizeIn32BitWords = 4,
  kNvmInfoFieldCpDeviceIdSizeInBytes =
      kNvmInfoFieldCpDeviceIdSizeIn32BitWords * sizeof(uint32_t),

  /**
   * AST Individualize Patch Address Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldAstIndividPatchAddrStartOffset = 400,
  kNvmInfoFieldAstIndividPatchAddrSizeIn32BitWords = 1,

  /**
   * AST Individualize Patch Value Start / Size - Bank 0, Page 0
   */
  kNvmInfoFieldAstIndividPatchValStartOffset = 404,
  kNvmInfoFieldAstIndividPatchValSizeIn32BitWords = 1,

  // Creator/Owner Seeds - Bank 0, Pages 1 and 2
  kNvmInfoFieldKeySeedSizeIn32BitWords = 32 / sizeof(uint32_t),

  // Wafer Authentication Secret - Bank 0, Page 3
  kNvmInfoFieldWaferAuthSecretSizeIn32BitWords = 32 / sizeof(uint32_t),

  // Attestation key gen seed indices
  kNvmInfoFieldUdsKeySeedIdx = 0,
  kNvmInfoFieldCdi0KeySeedIdx = 1,
  kNvmInfoFieldCdi1KeySeedIdx = 2,
  kNvmInfoFieldTpmEkKeySeedIdx = 3,
};

// Info Page 0 fields.
extern const nvm_info_field_t kNvmInfoFieldLotName;
extern const nvm_info_field_t kNvmInfoFieldWaferNumber;
extern const nvm_info_field_t kNvmInfoFieldWaferXCoord;
extern const nvm_info_field_t kNvmInfoFieldWaferYCoord;
extern const nvm_info_field_t kNvmInfoFieldProcessData;
extern const nvm_info_field_t kNvmInfoFieldAstCalibrationData;
extern const nvm_info_field_t kNvmInfoFieldAstCfgVersion;
extern const nvm_info_field_t kNvmInfoFieldCpDeviceId;
extern const nvm_info_field_t kNvmInfoFieldAstIndividPatchAddr;
extern const nvm_info_field_t kNvmInfoFieldAstIndividPatchVal;

// Info Page 1 fields.
extern const nvm_info_field_t kNvmInfoFieldCreatorSeed;

// Info Page 2 fields.
extern const nvm_info_field_t kNvmInfoFieldOwnerSeed;

// Info Page 3 fields.
extern const nvm_info_field_t kNvmInfoFieldWaferAuthSecret;

// Info Page 4 fields.
extern const nvm_info_field_t kNvmInfoFieldUdsAttestationKeySeed;
extern const nvm_info_field_t kNvmInfoFieldCdi0AttestationKeySeed;
extern const nvm_info_field_t kNvmInfoFieldCdi1AttestationKeySeed;
extern const nvm_info_field_t kNvmInfoFieldTpmEkAttestationKeySeed;
extern const nvm_info_field_t kNvmInfoFieldTpmCekAttestationKeySeed;
extern const nvm_info_field_t kNvmInfoFieldTpmCikAttestationKeySeed;
extern const nvm_info_field_t kNvmInfoFieldDevSeedSeed;
extern const nvm_info_field_t kNvmInfoFieldAttestationKeyGenVersion;

/**
 * Reads info NVM page field.
 *
 * Initialises a local NVM controller handle, configures the info region for
 * read access, then reads the requested words.
 *
 * @param field Flash info field information.
 * @param[out] data_out Output buffer.
 * @param num_words Number of words to read from NVM and write to `data_out`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_nvm_info_field_read(nvm_info_field_t field, uint32_t *data_out,
                                   size_t num_words);

/**
 * Write info NVM page field.
 *
 * Initialises a local NVM controller handle, configures the info region for
 * write/erase access, then writes the requested words.
 *
 * @param field Flash info field information.
 * @param data_in Input buffer.
 * @param num_words Number of words to write from `data_in` to NVM.
 * @param erase_page_before_write Whether to erase the page before writing it.
 * @param readback Read back and verify data after writing. Set false for pages
 *                 not readable in the current LC state (e.g. WaferAuthSecret
 *                 in TEST_UNLOCKED).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_nvm_info_field_write(nvm_info_field_t field, uint32_t *data_in,
                                    size_t num_words,
                                    bool erase_page_before_write,
                                    bool readback);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_NVM_INFO_FIELD_H_
