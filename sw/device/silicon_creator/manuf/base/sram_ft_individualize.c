// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/base/ft_device_id.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/ast_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_otp_ctrl_t otp_ctrl;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  return OK_STATUS();
}

/**
 * Patch AST config if patch exists in flash info page 0.
 */
static status_t patch_ast_config_value(void) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldAstIndividPatchAddr.page,
      kFlashInfoFieldAstIndividPatchAddr.bank,
      kFlashInfoFieldAstIndividPatchAddr.partition, kFlashInfoPage0Permissions,
      &byte_address));

  // Read patch address and value from flash info 0.
  uint32_t ast_patch_addr_offset;
  uint32_t ast_patch_value;
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstIndividPatchAddr,
      &ast_patch_addr_offset,
      kFlashInfoFieldAstIndividPatchAddrSizeIn32BitWords));
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstIndividPatchVal, &ast_patch_value,
      kFlashInfoFieldAstIndividPatchValSizeIn32BitWords));

  // Check the address is within range before programming.
  if (kDeviceType == kDeviceSilicon || kDeviceType == kDeviceSimDV) {
    TRY_CHECK(ast_patch_addr_offset <= AST_REGAL_REG_OFFSET);
  }

  // Only patch AST if the patch value is present.
  if (ast_patch_value != 0 && ast_patch_value != UINT32_MAX) {
    // Write patch value.
    abs_mmio_write32(
        TOP_EARLGREY_AST_BASE_ADDR + ast_patch_addr_offset * sizeof(uint32_t),
        ast_patch_value);
  }

  return OK_STATUS();
}

/**
 * Provision OTP {CreatorSw,OwnerSw,Hw}Cfg and RotCreatorAuth{Codesign,State}
 * partitions.
 *
 * Note: CreatorSwCfg and OwnerSwCfg partitions are not locked yet, as not
 * all fields can be programmed until the personalization stage.
 */
static status_t provision(void) {
  // Patch AST config if requested.
  TRY(patch_ast_config_value());

  // Perform OTP writes.
  LOG_INFO("Writing HW_CFG* OTP partitions ...");
  TRY(manuf_individualize_device_hw_cfg(
      &flash_ctrl_state, &otp_ctrl, kFlashInfoPage0Permissions, kFtDeviceId));
  LOG_INFO("Writing ROT_CREATOR_AUTH_CODESIGN OTP partition ...");
  TRY(manuf_individualize_device_rot_creator_auth_codesign(&otp_ctrl));
  LOG_INFO("Writing ROT_CREATOR_AUTH_STATE OTP partition ...");
  TRY(manuf_individualize_device_rot_creator_auth_state(&otp_ctrl));
  LOG_INFO("Writing OWNER_SW_CFG OTP partition ...");
  TRY(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
  LOG_INFO("Writing CREATOR_SW_CFG OTP partition ...");
  TRY(manuf_individualize_device_creator_sw_cfg(&otp_ctrl, &flash_ctrl_state));
  LOG_INFO("FT SRAM provisioning done.");

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init());
  ottf_console_init();

  // Perform provisioning operations.
  CHECK_STATUS_OK(provision());

  // Halt the CPU here to enable JTAG to perform an LC transition to mission
  // mode, as ROM execution should be active now.
  abort();

  return true;
}
