// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/isolated_flash_partition.h"

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

status_t isolated_flash_partition_read(dif_flash_ctrl_state_t *flash_ctrl_state,
                                       size_t num_words,
                                       uint32_t *wafer_auth_secret) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_ctrl_state, /*page_id=*/kFlashInfoWaferAuthSecretPageId,
      /*bank=*/kFlashInfoWaferAuthSecretBankId,
      /*partition_id=*/kFlashInfoWaferAuthSecretPartitionId,
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
      /*partition_id=*/kFlashInfoWaferAuthSecretPartitionId, wafer_auth_secret,
      /*partition_type=*/kDifFlashCtrlPartitionTypeInfo, num_words,
      /*delay_micros=*/0));

  return OK_STATUS();
}

status_t isolated_flash_partition_write(
    dif_flash_ctrl_state_t *flash_ctrl_state, const uint32_t *wafer_auth_secret,
    size_t num_words) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_ctrl_state, /*page_id=*/kFlashInfoWaferAuthSecretPageId,
      /*bank=*/kFlashInfoWaferAuthSecretBankId,
      /*partition_id=*/kFlashInfoWaferAuthSecretPartitionId,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4True,
          .prog_en = kMultiBitBool4True,
          .rd_en = kMultiBitBool4False,
          .scramble_en = kMultiBitBool4False},
      &byte_address));
  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash_ctrl_state, byte_address,
      /*partition_id=*/kFlashInfoWaferAuthSecretPartitionId, wafer_auth_secret,
      kDifFlashCtrlPartitionTypeInfo, num_words));

  return OK_STATUS();
}
