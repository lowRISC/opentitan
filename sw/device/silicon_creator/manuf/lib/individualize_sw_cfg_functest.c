// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

/**
 * DIF Handles.
 *
 * Keep this list sorted in alphabetical order.
 */
static dif_otp_ctrl_t otp_ctrl;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_rstmgr_t rstmgr;

static dif_flash_ctrl_region_properties_t kFlashInfoPage0Permissions = {
    .ecc_en = kMultiBitBool4True,
    .high_endurance_en = kMultiBitBool4False,
    .erase_en = kMultiBitBool4True,
    .prog_en = kMultiBitBool4True,
    .rd_en = kMultiBitBool4True,
    .scramble_en = kMultiBitBool4False};

enum {
  kNumAstCfgWords = 3,
  kAstCfgBufferSizeIn32BitWords = (kNumAstCfgWords * 2) + 1,

  // AST configuration word 0 to test.
  kAstCfgRelativeAddr0 = 0x4,
  kAstCfgOtpAddr0 =
      OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_OFFSET + kAstCfgRelativeAddr0,
  kAstCfgAddr0 = TOP_EARLGREY_AST_BASE_ADDR + kAstCfgRelativeAddr0,
  kAstCfgData0 = 0xcafebeef,

  // AST configuration word 1 to test.
  kAstCfgRelativeAddr1 = 0x40,
  kAstCfgOtpAddr1 =
      OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_OFFSET + kAstCfgRelativeAddr1,
  kAstCfgAddr1 = TOP_EARLGREY_AST_BASE_ADDR + kAstCfgRelativeAddr1,
  kAstCfgData1 = 0xdeadbeef,

  // AST configuration word 2 to test.
  kAstCfgRelativeAddr2 = 0x20,
  kAstCfgOtpAddr2 =
      OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_OFFSET + kAstCfgRelativeAddr2,
  kAstCfgAddr2 = TOP_EARLGREY_AST_BASE_ADDR + kAstCfgRelativeAddr2,
  kAstCfgData2 = 0x12345678,
};

static uint32_t ast_cfg_data[kAstCfgBufferSizeIn32BitWords] = {
    kNumAstCfgWords, kAstCfgAddr0, kAstCfgData0, kAstCfgAddr1,
    kAstCfgData1,    kAstCfgAddr2, kAstCfgData2};

/**
 * Initializes all DIF handles used in this module.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  return OK_STATUS();
}

/**
 * Initializes flash info page 0 fields required to complete the
 * individualization step.
 */
static status_t init_flash_info_page0(void) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldAstCalibrationData.page,
      kFlashInfoFieldAstCalibrationData.bank,
      kFlashInfoFieldAstCalibrationData.partition, kFlashInfoPage0Permissions,
      &byte_address));
  TRY(flash_ctrl_testutils_erase_page(
      &flash_ctrl_state, byte_address,
      kFlashInfoFieldAstCalibrationData.partition,
      kDifFlashCtrlPartitionTypeInfo));
  TRY(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      byte_address + kFlashInfoFieldAstCalibrationData.byte_offset,
      kFlashInfoFieldAstCalibrationData.partition, ast_cfg_data,
      kDifFlashCtrlPartitionTypeInfo, kAstCfgBufferSizeIn32BitWords));
  return OK_STATUS();
}

/**
 * Check the AST configuration data was programmed correctly.
 */
static status_t check_otp_ast_cfg(void) {
  uint32_t data;
  uint32_t relative_addr;

  // Check AST config value 0.
  TRY(dif_otp_ctrl_relative_address(kDifOtpCtrlPartitionCreatorSwCfg,
                                    kAstCfgOtpAddr0, &relative_addr));
  TRY(otp_ctrl_testutils_dai_read32(&otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
                                    relative_addr, &data));
  TRY_CHECK(data == kAstCfgData0);

  // Check AST config value 1.
  TRY(dif_otp_ctrl_relative_address(kDifOtpCtrlPartitionCreatorSwCfg,
                                    kAstCfgOtpAddr1, &relative_addr));
  TRY(otp_ctrl_testutils_dai_read32(&otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
                                    relative_addr, &data));
  TRY_CHECK(data == kAstCfgData1);

  // Check AST config value 2.
  TRY(dif_otp_ctrl_relative_address(kDifOtpCtrlPartitionCreatorSwCfg,
                                    kAstCfgOtpAddr2, &relative_addr));
  TRY(otp_ctrl_testutils_dai_read32(&otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
                                    relative_addr, &data));
  TRY_CHECK(data == kAstCfgData2);

  return OK_STATUS();
}

/**
 * Perform software reset.
 */
static void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());

  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    CHECK_STATUS_OK(init_flash_info_page0());
    CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg(
        &otp_ctrl, &flash_ctrl_state));
    CHECK_STATUS_OK(
        manuf_individualize_device_flash_data_default_cfg(&otp_ctrl));
    CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg_lock(&otp_ctrl));
    CHECK_STATUS_OK(check_otp_ast_cfg());
    LOG_INFO("Provisioned and locked CREATOR_SW_CFG OTP partition.");
    // Halt the CPU here to enable host to perform POR and bootstrap again since
    // flash scrambling enablement has changed.
    abort();
  }

  if (!status_ok(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl))) {
    CHECK_STATUS_OK(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
    LOG_INFO("Provisioned and locked OWNER_SW_CFG OTP partition.");
    // Perform SW reset to complete locking of the OWNER_SW_CFG partition.
    sw_reset();
  }

  if (status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl)) &&
      status_ok(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl))) {
    return true;
  }
  return false;
}
