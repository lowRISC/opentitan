// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/data/ast/calibration_values.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  return OK_STATUS();
}

static void manually_init_ast(uint32_t *data) {
  for (size_t i = 0; i < kFlashInfoAstCalibrationDataSizeIn32BitWords; ++i) {
    abs_mmio_write32(TOP_EARLGREY_AST_BASE_ADDR + i * sizeof(uint32_t),
                     data[i]);
  }
}

static status_t flash_info_page_0_erase(void) {
  uint32_t byte_address = 0;
  // DeviceId and ManufState are located on the same flash info page.
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldDeviceId.page,
      kFlashInfoFieldDeviceId.bank, kFlashInfoFieldDeviceId.partition,
      kFlashInfoPage0Permissions, &byte_address));
  TRY(flash_ctrl_testutils_erase_page(&flash_ctrl_state, byte_address,
                                      kFlashInfoFieldDeviceId.partition,
                                      kDifFlashCtrlPartitionTypeInfo));
  return OK_STATUS();
}

static status_t flash_info_page_0_write(
    manuf_cp_provisioning_data_t *provisioning_data) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldDeviceId.page,
      kFlashInfoFieldDeviceId.bank, kFlashInfoFieldDeviceId.partition,
      kFlashInfoPage0Permissions, &byte_address));

  // Write DeviceId.
  TRY(flash_ctrl_testutils_write(
      &flash_ctrl_state, byte_address, kFlashInfoFieldDeviceId.partition,
      provisioning_data->device_id, kDifFlashCtrlPartitionTypeInfo,
      kHwCfgDeviceIdSizeIn32BitWords));

  // Write ManufState (on same page as DeviceId).
  TRY(flash_ctrl_testutils_write(
      &flash_ctrl_state, byte_address + kFlashInfoFieldManufState.byte_offset,
      kFlashInfoFieldManufState.partition, provisioning_data->manuf_state,
      kDifFlashCtrlPartitionTypeInfo, kHwCfgManufStateSizeIn32BitWords));

  // Write AST calibration values (on same page as DeviceId).
  TRY(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      byte_address + kFlashInfoFieldAstCalibrationData.byte_offset,
      kFlashInfoFieldAstCalibrationData.partition, ast_cfg_data,
      kDifFlashCtrlPartitionTypeInfo,
      kFlashInfoAstCalibrationDataSizeIn32BitWords));

  return OK_STATUS();
}

static status_t wafer_auth_secret_flash_info_page_erase(void) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret.page,
      kFlashInfoFieldWaferAuthSecret.bank,
      kFlashInfoFieldWaferAuthSecret.partition, kFlashInfoPage3WritePermissions,
      &byte_address));
  TRY(flash_ctrl_testutils_erase_page(&flash_ctrl_state, byte_address,
                                      kFlashInfoFieldWaferAuthSecret.partition,
                                      kDifFlashCtrlPartitionTypeInfo));
  return OK_STATUS();
}

static status_t wafer_auth_secret_flash_info_page_write(
    manuf_cp_provisioning_data_t *provisioning_data) {
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret.page,
      kFlashInfoFieldWaferAuthSecret.bank,
      kFlashInfoFieldWaferAuthSecret.partition, kFlashInfoPage3WritePermissions,
      &byte_address));
  TRY(flash_ctrl_testutils_write(
      &flash_ctrl_state, byte_address, kFlashInfoFieldWaferAuthSecret.partition,
      provisioning_data->manuf_state, kDifFlashCtrlPartitionTypeInfo,
      kFlashInfoWaferAuthSecretSizeIn32BitWords));
  return OK_STATUS();
}

static status_t print_inputs_to_console(
    manuf_cp_provisioning_data_t *provisioning_data) {
  uint32_t high;
  uint32_t low;

  LOG_INFO("Device ID:");
  for (size_t i = 0; i < kHwCfgDeviceIdSizeIn32BitWords; ++i) {
    LOG_INFO("0x%x", provisioning_data->device_id[i]);
  }
  LOG_INFO("Test Unlock Token Hash:");
  for (size_t i = 0; i < ARRAYSIZE(provisioning_data->test_unlock_token_hash);
       ++i) {
    high = provisioning_data->test_unlock_token_hash[i] >> 32;
    low = provisioning_data->test_unlock_token_hash[i] & 0xffffffff;
    LOG_INFO("0x%x%x", high, low);
  }
  LOG_INFO("Test Exit Token Hash:");
  for (size_t i = 0; i < ARRAYSIZE(provisioning_data->test_exit_token_hash);
       ++i) {
    high = provisioning_data->test_exit_token_hash[i] >> 32;
    low = provisioning_data->test_exit_token_hash[i] & 0xffffffff;
    LOG_INFO("0x%x%x", high, low);
  }
  return OK_STATUS();
}

/**
 * Provision flash info pages 0 and 3, and OTP Secret0 partition.
 */
static status_t provision(ujson_t *uj) {
  LOG_INFO("Waiting for CP provisioning data ...");
  manuf_cp_provisioning_data_t provisioning_data;
  TRY(ujson_deserialize_manuf_cp_provisioning_data_t(uj, &provisioning_data));
  TRY(print_inputs_to_console(&provisioning_data));
  TRY(flash_ctrl_testutils_wait_for_init(&flash_ctrl_state));
  TRY(flash_info_page_0_erase());
  TRY(wafer_auth_secret_flash_info_page_erase());
  TRY(flash_info_page_0_write(&provisioning_data));
  TRY(wafer_auth_secret_flash_info_page_write(&provisioning_data));
  TRY(manuf_individualize_device_secret0(&lc_ctrl, &otp_ctrl,
                                         &provisioning_data));
  LOG_INFO("CP provisioning done.");
  return OK_STATUS();
}

bool test_main(void) {
  // Initialize AST, DIF handles, pinmux, and UART.
  manually_init_ast(ast_cfg_data);
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();
  LOG_INFO("AST manually configured.");

  // Perform CP provisioning operations.
  CHECK_STATUS_OK(provision(&uj));

  return true;
}
