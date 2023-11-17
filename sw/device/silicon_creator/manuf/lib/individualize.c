// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/individualize.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/silicon_creator/manuf/lib/util.h"

#include "otp_ctrl_regs.h"

typedef struct hw_cfg_settings {
  /**
   * Enable / disable execute from SRAM CSR switch.
   */
  multi_bit_bool_t en_sram_ifetch;
  /**
   * This input efuse is used to enable access to the NIST internal state per
   * instance.
   */
  multi_bit_bool_t en_csrng_sw_app_read;
  /**
   * This input efuse is used to enable access to the ENTROPY_DATA register
   * directly.
   */
  multi_bit_bool_t en_entropy_src_fw_read;
  /**
   * This input efuse is used to enable access to the firmware override FIFO and
   * other related functions.
   */
  multi_bit_bool_t en_entropy_src_fw_over;
} hw_cfg_settings_t;

// Changing any of the following values may result in unexpected device
// behavior.
//
// - en_sram_ifetch: required to enable SRAM code execution during
//   manufacturing.
// - en_csrng_sw_app_read: required to be able to extract output from CSRNG.
// - en_entropy_src_fw_read and en_entropy_src_fw_over: Required to implement
//   entropy_src conditioner KAT.
const hw_cfg_settings_t kHwCfgSettings = {
    .en_sram_ifetch = kMultiBitBool8True,
    .en_csrng_sw_app_read = kMultiBitBool8True,
    .en_entropy_src_fw_read = kMultiBitBool8True,
    .en_entropy_src_fw_over = kMultiBitBool8True,
};

/**
 * Configures digital logic settings in the HW_CFG partition.
 *
 * @param otp OTP controller instance.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static status_t hw_cfg_enable_knobs_set(const dif_otp_ctrl_t *otp_ctrl) {
  uint32_t val =
      bitfield_field32_write(0, kSramFetch, kHwCfgSettings.en_sram_ifetch);
  val = bitfield_field32_write(val, kCsrngAppRead,
                               kHwCfgSettings.en_csrng_sw_app_read);
  val = bitfield_field32_write(val, kEntropySrcFwRd,
                               kHwCfgSettings.en_entropy_src_fw_read);
  val = bitfield_field32_write(val, kEntropySrcFwOvr,
                               kHwCfgSettings.en_entropy_src_fw_over);

  TRY(otp_ctrl_testutils_dai_write32(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                     kHwCfgEnSramIfetchOffset, &val,
                                     /*len=*/1));
  return OK_STATUS();
}

status_t manuf_individualize_device_hw_cfg(
    dif_flash_ctrl_state_t *flash_state, const dif_otp_ctrl_t *otp_ctrl,
    dif_flash_ctrl_region_properties_t flash_info_page_0_permissions,
    uint32_t *device_id) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Configure byte-sized hardware enable knobs.
  TRY(hw_cfg_enable_knobs_set(otp_ctrl));

  // Configure flash info page permissions in case we started from a cold boot.
  // Note: device_id and manuf_state are on the same flash info page.
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_state, kFlashInfoFieldDeviceId.page, kFlashInfoFieldDeviceId.bank,
      kFlashInfoFieldDeviceId.partition, flash_info_page_0_permissions,
      /*offset=*/NULL));

  // Configure DeviceID
  uint32_t device_id_from_flash[kHwCfgDeviceIdSizeIn32BitWords];
  uint32_t empty_device_id[kHwCfgDeviceIdSizeIn32BitWords] = {0};
  TRY(manuf_flash_info_field_read(flash_state, kFlashInfoFieldDeviceId,
                                  device_id_from_flash,
                                  kHwCfgDeviceIdSizeIn32BitWords));
  bool flash_device_id_empty = true;
  for (size_t i = 0;
       flash_device_id_empty && i < kHwCfgDeviceIdSizeIn32BitWords; ++i) {
    flash_device_id_empty &= device_id_from_flash[i] == 0;
  }

  // If the device ID read from flash is non-empty, then it must match the
  // device ID provided. If the device ID read from flash is empty, we check to
  // ensure the device ID provided is also not empty. An empty (all zero) device
  // ID will prevent the keymgr from advancing.
  if (!flash_device_id_empty) {
    TRY_CHECK_ARRAYS_EQ(device_id_from_flash, device_id,
                        kHwCfgDeviceIdSizeIn32BitWords);
  } else {
    TRY_CHECK_ARRAYS_NE(device_id, empty_device_id,
                        kHwCfgDeviceIdSizeIn32BitWords);
  }
  TRY(otp_ctrl_testutils_dai_write32(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                     kHwCfgDeviceIdOffset, device_id,
                                     kHwCfgDeviceIdSizeIn32BitWords));

  // Configure ManufState
  uint32_t manuf_state[kHwCfgManufStateSizeIn32BitWords];
  TRY(manuf_flash_info_field_read(flash_state, kFlashInfoFieldManufState,
                                  manuf_state,
                                  kHwCfgManufStateSizeIn32BitWords));
  TRY(otp_ctrl_testutils_dai_write32(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                     kHwCfgManufStateOffset, manuf_state,
                                     kHwCfgManufStateSizeIn32BitWords));

  TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                        /*digest=*/0));
  return OK_STATUS();
}

status_t manuf_individualize_device_hw_cfg_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  // TODO: Add DeviceId by comparing OTP flash value against the value reported
  // by lc_ctrl. Consider erasing the data from the flash info pages.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg,
                                      &is_locked));
  uint64_t digest;
  TRY(dif_otp_ctrl_get_digest(otp_ctrl, kDifOtpCtrlPartitionHwCfg, &digest));

  return is_locked ? OK_STATUS() : INTERNAL();
}

status_t manuf_individualize_device_secret0(
    const dif_lc_ctrl_t *lc_ctrl, const dif_otp_ctrl_t *otp_ctrl,
    const manuf_cp_provisioning_data_t *provisioning_data) {
  // Check life cycle in TEST_UNLOCKED0.
  TRY(lc_ctrl_testutils_check_lc_state(lc_ctrl, kDifLcCtrlStateTestUnlocked0));

  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  uint64_t hashed_test_unlock_token[kSecret0TestUnlockTokenSizeIn64BitWords];
  uint64_t hashed_test_exit_token[kSecret0TestExitTokenSizeIn64BitWords];
  TRY(manuf_util_hash_lc_transition_token(provisioning_data->test_unlock_token,
                                          kSecret0TestUnlockTokenSizeInBytes,
                                          hashed_test_unlock_token));
  TRY(manuf_util_hash_lc_transition_token(provisioning_data->test_exit_token,
                                          kSecret0TestExitTokenSizeInBytes,
                                          hashed_test_exit_token));

  TRY(otp_ctrl_testutils_dai_write64(
      otp_ctrl, kDifOtpCtrlPartitionSecret0, kSecret0TestUnlockTokenOffset,
      hashed_test_unlock_token, kSecret0TestUnlockTokenSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(
      otp_ctrl, kDifOtpCtrlPartitionSecret0, kSecret0TestExitTokenOffset,
      hashed_test_exit_token, kSecret0TestExitTokenSizeIn64BitWords));

  TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t manuf_individualize_device_secret0_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                      &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}
