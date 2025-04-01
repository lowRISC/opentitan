// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/base/ft_device_id.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/ast_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_gpio_t gpio;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

// ATE Indicator GPIOs.
static const dif_gpio_pin_t kGpioPinTestStart = 0;
static const dif_gpio_pin_t kGpioPinTestDone = 1;
static const dif_gpio_pin_t kGpioPinTestError = 2;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  return OK_STATUS();
}

/**
 * Configure the ATE GPIO indicator pins.
 */
static status_t configure_ate_gpio_indicators(void) {
  // IOA0 / GPIO2 is for error reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa0,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestError));
  // IOA1 / GPIO1 is for test done reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa1,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestDone));
  // IOA4 / GPIO0 is for test start reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa4,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestStart));
  TRY(dif_gpio_output_set_enabled_all(&gpio,
                                      0x7));        // Enable first three GPIOs.
  TRY(dif_gpio_write_all(&gpio, /*write_val=*/0));  // Intialize all to 0.
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

  // Only patch AST if the patch value is present.
  if (ast_patch_value != 0 && ast_patch_value != UINT32_MAX) {
    // Check the address is within range before programming.
    if (kDeviceType == kDeviceSilicon || kDeviceType == kDeviceSimDV) {
      TRY_CHECK(ast_patch_addr_offset <= AST_REGAL_REG_OFFSET);
    }
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
  TRY(manuf_individualize_device_hw_cfg(
      &flash_ctrl_state, &otp_ctrl, kFlashInfoPage0Permissions, kFtDeviceId));
  TRY(manuf_individualize_device_rot_creator_auth_codesign(&otp_ctrl));
  TRY(manuf_individualize_device_rot_creator_auth_state(&otp_ctrl));
  TRY(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
  TRY(manuf_individualize_device_creator_sw_cfg(&otp_ctrl, &flash_ctrl_state));

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init());
  CHECK_STATUS_OK(configure_ate_gpio_indicators());

  // Perform provisioning operations.
  CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestStart, true));
  status_t result = provision();
  if (!status_ok(result)) {
    CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestError, true));
  } else {
    CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestDone, true));
  }
  return true;
}
