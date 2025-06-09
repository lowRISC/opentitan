// Copyright lowRISC contributors (OpenTitan project).
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

#include "hw/top/otp_ctrl_regs.h"

typedef struct hw_cfg1_settings {
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
   * This efuse is to disable the RV_DM late debug enable behavior
   */
  multi_bit_bool_t dis_rv_dm_late_debug;
} hw_cfg1_settings_t;

// Changing any of the following values may result in unexpected device
// behavior.
//
// - en_sram_ifetch: required to enable SRAM code execution during
//   manufacturing.
// - en_csrng_sw_app_read: required to be able to extract output from CSRNG.
const hw_cfg1_settings_t kHwCfg1Settings = {
    .en_sram_ifetch = kMultiBitBool8True,
    .en_csrng_sw_app_read = kMultiBitBool8True,
    .dis_rv_dm_late_debug = kMultiBitBool8True,
};

/**
 * Configures digital logic settings in the HW_CFG1 partition.
 *
 * @param otp OTP controller instance.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static status_t hw_cfg1_enable_knobs_set(const dif_otp_ctrl_t *otp_ctrl) {
  uint32_t val =
      bitfield_field32_write(0, kSramFetch, kHwCfg1Settings.en_sram_ifetch);
  val = bitfield_field32_write(val, kCsrngAppRead,
                               kHwCfg1Settings.en_csrng_sw_app_read);
  val = bitfield_field32_write(val, kDisRvDmLateDebug,
                               kHwCfg1Settings.dis_rv_dm_late_debug);

  TRY(otp_ctrl_testutils_dai_write32(otp_ctrl, kDifOtpCtrlPartitionHwCfg1,
                                     kHwCfgEnSramIfetchOffset, &val,
                                     /*len=*/1));
  return OK_STATUS();
}

status_t manuf_individualize_device_hw_cfg(
    dif_flash_ctrl_state_t *flash_state, const dif_otp_ctrl_t *otp_ctrl,
    dif_flash_ctrl_region_properties_t flash_info_page_0_permissions,
    const uint32_t *ft_device_id) {
  bool is_locked;

  // Provision HW_CFG0 if it is not locked.
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                      &is_locked));
  if (!is_locked) {
    // Configure flash info page permissions in case we started from a cold
    // boot. Note: cp_device_id and manuf_state are on the same flash info page.
    TRY(flash_ctrl_testutils_info_region_setup_properties(
        flash_state, kFlashInfoFieldCpDeviceId.page,
        kFlashInfoFieldCpDeviceId.bank, kFlashInfoFieldCpDeviceId.partition,
        flash_info_page_0_permissions,
        /*offset=*/NULL));

    // Read CpDeviceId & AST configuration version from flash info page 0.
    uint32_t cp_device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords];
    TRY(manuf_flash_info_field_read(flash_state, kFlashInfoFieldCpDeviceId,
                                    cp_device_id,
                                    kFlashInfoFieldCpDeviceIdSizeIn32BitWords));
    uint32_t ast_cfg_version;
    TRY(manuf_flash_info_field_read(
        flash_state, kFlashInfoFieldAstCfgVersion, &ast_cfg_version,
        kFlashInfoFieldAstCfgVersionSizeIn32BitWords));

    // Check if AST configuration version is an 8-bit value.
    if (ast_cfg_version > UINT8_MAX) {
      return OUT_OF_RANGE();
    }

    // Check if CP device ID from flash is empty.
    bool flash_cp_device_id_empty = true;
    for (size_t i = 0; i < kFlashInfoFieldCpDeviceIdSizeIn32BitWords; ++i) {
      if (cp_device_id[i] != 0) {
        flash_cp_device_id_empty = false;
        break;
      }
    }

    // On non-silicon targets, we expect the CP device ID from flash to be
    // empty. In this case we set the HW origin and DIN portions of the CP
    // device ID to all 1s to indicate this is an FPGA/Sim generated device ID.
    // Otherwise, we expect the CP device ID to be present and non-zero.
    if (flash_cp_device_id_empty) {
      if (kDeviceType != kDeviceSilicon && kDeviceType != kDeviceSimDV) {
        memset(&cp_device_id, 0, sizeof(cp_device_id));
        cp_device_id[0] = UINT32_MAX;
        cp_device_id[1] = UINT32_MAX;
        cp_device_id[2] = UINT32_MAX;
      } else {
        return NOT_FOUND();
      }
    }

    // Construct the complete device ID.
    uint32_t device_id[kHwCfgDeviceIdSizeIn32BitWords];
    memcpy(device_id, cp_device_id, kFlashInfoFieldCpDeviceIdSizeInBytes);
    // CP and FT device IDs are the same length (128 bit words).
    memcpy(&device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords], ft_device_id,
           kFlashInfoFieldCpDeviceIdSizeInBytes);

    // Overwrite AST configuration version field in FT device ID with the
    // version field from flash.
    uint32_t ft_device_id_mask = 0xFFFF00FF;
    device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords] =
        (device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords] &
         ft_device_id_mask) |
        (ast_cfg_version << 8);

    // Write the complete device ID to OTP.
    TRY(otp_ctrl_testutils_dai_write32(otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                       kHwCfgDeviceIdOffset, device_id,
                                       kHwCfgDeviceIdSizeIn32BitWords));

    // Configure ManufState as all 0s. It is unused.
    uint32_t manuf_state[kHwCfgManufStateSizeIn32BitWords] = {0};
    TRY(otp_ctrl_testutils_dai_write32(otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                       kHwCfgManufStateOffset, manuf_state,
                                       kHwCfgManufStateSizeIn32BitWords));
    TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                          /*digest=*/0));
  }

  // Provision HW_CFG1 if it is not locked.
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg1,
                                      &is_locked));
  if (!is_locked) {
    // Configure byte-sized hardware enable knobs.
    TRY(hw_cfg1_enable_knobs_set(otp_ctrl));

    TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionHwCfg1,
                                          /*digest=*/0));
  }
  return OK_STATUS();
}

status_t manuf_individualize_device_hw_cfg_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  // TODO: Add DeviceId by comparing OTP flash value against the value reported
  // by lc_ctrl. Consider erasing the data from the flash info pages.
  bool is_locked0, is_locked1;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                      &is_locked0));
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg1,
                                      &is_locked1));
  uint64_t digest0, digest1;
  TRY(dif_otp_ctrl_get_digest(otp_ctrl, kDifOtpCtrlPartitionHwCfg0, &digest0));
  TRY(dif_otp_ctrl_get_digest(otp_ctrl, kDifOtpCtrlPartitionHwCfg1, &digest1));

  return is_locked0 && is_locked1 ? OK_STATUS() : INTERNAL();
}

status_t manuf_individualize_device_secret0(
    const dif_lc_ctrl_t *lc_ctrl, const dif_otp_ctrl_t *otp_ctrl,
    const manuf_cp_provisioning_data_t *provisioning_data) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                     kSecret0TestUnlockTokenOffset,
                                     provisioning_data->test_unlock_token_hash,
                                     kSecret0TestUnlockTokenSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret0,
                                     kSecret0TestExitTokenOffset,
                                     provisioning_data->test_exit_token_hash,
                                     kSecret0TestExitTokenSizeIn64BitWords));

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
