// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include <stdint.h>

#include "otp_ctrl_regs.h"  // Generated.

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
