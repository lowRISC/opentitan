// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_SKUS_EARLGREY_A0_GENERIC_CONSTS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_SKUS_EARLGREY_A0_GENERIC_CONSTS_H_

#include "sw/device/lib/dif/dif_flash_ctrl.h"

/**
 * Access permissions for flash info page 0 (holds device_id and manuf_state).
 */
dif_flash_ctrl_region_properties_t kFlashInfoPage0Permissions = {
    .ecc_en = kMultiBitBool4True,
    .high_endurance_en = kMultiBitBool4False,
    .erase_en = kMultiBitBool4True,
    .prog_en = kMultiBitBool4True,
    .rd_en = kMultiBitBool4True,
    .scramble_en = kMultiBitBool4False};

/**
 * Access permissions for flash info page 3 (holds wafer_auth_secret).
 */
dif_flash_ctrl_region_properties_t kFlashInfoPage3WritePermissions = {
    .ecc_en = kMultiBitBool4True,
    .high_endurance_en = kMultiBitBool4False,
    .erase_en = kMultiBitBool4True,
    .prog_en = kMultiBitBool4True,
    .rd_en = kMultiBitBool4False,
    .scramble_en = kMultiBitBool4False};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_SKUS_EARLGREY_A0_GENERIC_CONSTS_H_
