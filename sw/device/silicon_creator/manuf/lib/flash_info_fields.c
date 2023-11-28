// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/silicon_creator/lib/attestation.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "otp_ctrl_regs.h"    // Generated.

// Ensure all the fields in the manuf page fit.
// static_assert((OTP_CTRL_PARAM_DEVICE_ID_SIZE +
static_assert((OTP_CTRL_PARAM_DEVICE_ID_SIZE + OTP_CTRL_PARAM_MANUF_STATE_SIZE +
               kFlashInfoFieldMaxAstCalibrationDataSizeInBytes) <=
                  FLASH_CTRL_PARAM_BYTES_PER_PAGE,
              "Last field (AST calibration data) in manuf page does not fit.");

/**
 * Partition 0 pages and fields.
 * Refer to sw/device/silicon_creator/lib/drivers/flash_ctrl.h for what
 * information ROM and ROM_EXT expect to find on various pages.
 */
const flash_info_field_t kFlashInfoFieldDeviceId = {
    .partition = 0,
    .bank = 0,
    .page = 0,
    .byte_offset = 0,
};

const flash_info_field_t kFlashInfoFieldManufState = {
    .partition = 0,
    .bank = 0,
    .page = 0,
    .byte_offset = OTP_CTRL_PARAM_DEVICE_ID_SIZE,
};

const flash_info_field_t kFlashInfoFieldAstCalibrationData = {
    .partition = 0,
    .bank = 0,
    .page = 0,
    .byte_offset =
        OTP_CTRL_PARAM_DEVICE_ID_SIZE + OTP_CTRL_PARAM_MANUF_STATE_SIZE,
};

const flash_info_field_t kFlashInfoFieldCreatorSeed = {
    .partition = 0,
    .bank = 0,
    .page = 1,
    .byte_offset = 0,
};

const flash_info_field_t kFlashInfoFieldOwnerSeed = {
    .partition = 0,
    .bank = 0,
    .page = 2,
    .byte_offset = 0,
};

const flash_info_field_t kFlashInfoFieldWaferAuthSecret = {
    .partition = 0,
    .bank = 0,
    .page = 3,
    .byte_offset = 0,
};

const flash_info_field_t kFlashInfoFieldUdsAttestationKeySeed = {
    .partition = 0,
    .bank = 0,
    .page = 4,
    .byte_offset = 0,
};

const flash_info_field_t kFlashInfoFieldCdi0AttestationKeySeed = {
    .partition = 0,
    .bank = 0,
    .page = 4,
    .byte_offset = kAttestationSeedBytes,
};

const flash_info_field_t kFlashInfoFieldCdi1AttestationKeySeed = {
    .partition = 0,
    .bank = 0,
    .page = 4,
    .byte_offset = (2 * kAttestationSeedBytes),
};

status_t manuf_flash_info_field_read(dif_flash_ctrl_state_t *flash_state,
                                     flash_info_field_t field,
                                     uint32_t *data_out, size_t num_words) {
  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      (field.page * device_info.bytes_per_page) + field.byte_offset;
  TRY(flash_ctrl_testutils_read(flash_state, byte_address, field.partition,
                                data_out, kDifFlashCtrlPartitionTypeInfo,
                                num_words,
                                /*delay=*/0));
  return OK_STATUS();
}
