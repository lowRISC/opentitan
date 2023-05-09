// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/isolated_flash_partition.h"

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"

enum {
  /**
   * Isolated partition ID.
   *
   * Used for wafer authentication secret.
   */
  kFlashInfoPartitionId = 0,

  /**
   * Isolated parition bank ID.
   *
   * Used for wafer authentication secret.
   */
  kFlashInfoBankId = 0,

  /**
   * Isolated partition flash info page ID.
   *
   * Used to store the wafer authentication secret
   */
  kFlashInfoPageIdWaferAuthSecret = 3,
};

status_t isolated_flash_partition_read(dif_flash_ctrl_state_t *flash_ctrl_state,
                                       size_t num_words,
                                       uint32_t *wafer_auth_secret) {
  // Enable read access to the flash isolated partition.
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_ctrl_state, /*page_id=*/kFlashInfoPageIdWaferAuthSecret,
      /*bank=*/kFlashInfoBankId, /*partition_id=*/kFlashInfoPartitionId,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4False,
          .prog_en = kMultiBitBool4False,
          .rd_en = kMultiBitBool4True,
          .scramble_en = kMultiBitBool4False},
      &byte_address));

  TRY(flash_ctrl_testutils_read(
      flash_ctrl_state, byte_address,
      /*partition_id=*/kFlashInfoPartitionId, wafer_auth_secret,
      /*partition_type=*/kDifFlashCtrlPartitionTypeInfo, num_words,
      /*delay_micros=*/0));

  // Disable read access to the flash isolated partition.
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_ctrl_state, /*page_id=*/kFlashInfoPageIdWaferAuthSecret,
      /*bank=*/kFlashInfoBankId, /*partition_id=*/kFlashInfoPartitionId,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4False,
          .prog_en = kMultiBitBool4False,
          .rd_en = kMultiBitBool4False,
          .scramble_en = kMultiBitBool4False},
      NULL));

  return OK_STATUS();
}

status_t isolated_flash_partition_write(
    dif_flash_ctrl_state_t *flash_ctrl_state, uint32_t *wafer_auth_secret,
    size_t num_words) {
  // Enable write access to the flash isolated partition.
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_ctrl_state, /*page_id=*/kFlashInfoPageIdWaferAuthSecret,
      /*bank=*/kFlashInfoBankId, /*partition_id=*/kFlashInfoPartitionId,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4False,
          .prog_en = kMultiBitBool4True,
          .rd_en = kMultiBitBool4False,
          .scramble_en = kMultiBitBool4False},
      &byte_address));

  TRY(flash_ctrl_testutils_write(
      flash_ctrl_state, byte_address,
      /*partition_id=*/kFlashInfoPartitionId, wafer_auth_secret,
      /*partition_type=*/kDifFlashCtrlPartitionTypeInfo, num_words));

  // Disable write access to the flash isolated partition.
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_ctrl_state, /*page_id=*/kFlashInfoPageIdWaferAuthSecret,
      /*bank=*/kFlashInfoBankId, /*partition_id=*/kFlashInfoPartitionId,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4False,
          .prog_en = kMultiBitBool4False,
          .rd_en = kMultiBitBool4False,
          .scramble_en = kMultiBitBool4False},
      NULL));

  return OK_STATUS();
}
