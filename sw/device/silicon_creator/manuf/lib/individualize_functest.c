// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * DIF Handles.
 *
 * Keep this list sorted in alphabetical order.
 */
static dif_flash_ctrl_state_t flash_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * CP and FT portions of the device ID are the same size.
 *
 * Note, the second byte of the FT device ID is set by the CP calibration step
 * and written to flash info page 0. We set it to 0x99 for testing.
 */
static const uint32_t kFtDeviceId[kFlashInfoFieldCpDeviceIdSizeIn32BitWords] = {
    0xAAAA99AA, 0xBBBBBBBB, 0xAAAAAAAA, 0xBBBBBBBB};

static dif_flash_ctrl_region_properties_t kFlashInfoPage0Permissions = {
    .ecc_en = kMultiBitBool4True,
    .high_endurance_en = kMultiBitBool4False,
    .erase_en = kMultiBitBool4True,
    .prog_en = kMultiBitBool4True,
    .rd_en = kMultiBitBool4True,
    .scramble_en = kMultiBitBool4False};

/**
 * Initializes all DIF handles used in this module.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  return OK_STATUS();
}

/**
 * Perform software reset.
 */
void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(
      lc_ctrl_testutils_check_lc_state(&lc_ctrl, kDifLcCtrlStateTestUnlocked1));

  if (!status_ok(manuf_individualize_device_hw_cfg_check(&otp_ctrl))) {
    // Setup page permissions on flash info page 0.
    uint32_t byte_address = 0;
    CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup_properties(
        &flash_state, kFlashInfoFieldCpDeviceId.page,
        kFlashInfoFieldCpDeviceId.bank, kFlashInfoFieldCpDeviceId.partition,
        kFlashInfoPage0Permissions, &byte_address));

    // Write the CP device ID to flash info page 0 and try to program HW_CFG0
    // partition.
    uint32_t kCpDeviceId[kFlashInfoFieldCpDeviceIdSizeIn32BitWords] = {
        0xAAAAAAAA, 0xBBBBBBBB, 0xAAAAAAAA, 0xBBBBBBBB};
    CHECK_STATUS_OK(manuf_flash_info_field_write(
        &flash_state, kFlashInfoFieldCpDeviceId, kCpDeviceId,
        kFlashInfoFieldCpDeviceIdSizeIn32BitWords,
        /*erase_page_before_write=*/true));
    uint32_t ast_cfg_version = 0x99;
    CHECK_STATUS_OK(manuf_flash_info_field_write(
        &flash_state, kFlashInfoFieldAstCfgVersion, &ast_cfg_version,
        kFlashInfoFieldAstCfgVersionSizeIn32BitWords,
        /*erase_page_before_write=*/false));
    CHECK_STATUS_OK(manuf_individualize_device_hw_cfg(
        &flash_state, &otp_ctrl, kFlashInfoPage0Permissions, kFtDeviceId));

    // Check the value of the DeviceId in the HW_CFG0 partition.
    uint32_t device_id[kHwCfgDeviceIdSizeIn32BitWords];
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32_array(
        &otp_ctrl, kDifOtpCtrlPartitionHwCfg0, 0, device_id,
        kHwCfgDeviceIdSizeIn32BitWords));
    LOG_INFO("CP Device ID in OTP: %08x%08x%08x%08x", device_id[3],
             device_id[2], device_id[2], device_id[0]);
    LOG_INFO("FT Device ID in OTP: %08x%08x%08x%08x", device_id[7],
             device_id[6], device_id[5], device_id[4]);
    CHECK_ARRAYS_EQ(device_id, kCpDeviceId,
                    kFlashInfoFieldCpDeviceIdSizeIn32BitWords);
    CHECK_ARRAYS_EQ(&device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords],
                    kFtDeviceId, kFlashInfoFieldCpDeviceIdSizeIn32BitWords);

    sw_reset();
  }

  return true;
}
