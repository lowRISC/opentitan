// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_command.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/silicon_creator/manuf/skus/earlgrey_a0/generic/consts.h"

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

static status_t device_id_and_manuf_state_flash_info_page_erase(
    manuf_cp_provisioning_data_t *provisioning_data) {
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

static status_t device_id_and_manuf_state_flash_info_page_write(
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

  return OK_STATUS();
}

static status_t wafer_auth_secret_flash_info_page_erase(
    manuf_cp_provisioning_data_t *provisioning_data) {
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

status_t command_processor(ujson_t *uj,
                           manuf_cp_provisioning_data_t *provisioning_data) {
  LOG_INFO("CP provisioning start. Waiting for command ...");
  while (true) {
    cp_provisioning_command_t command;
    TRY(ujson_deserialize_cp_provisioning_command_t(uj, &command));
    switch (command) {
      case kCpProvisioningCommandEraseAndWriteAll:
        // Write DeviceId, ManufState, & WaferAuthSecret to flash info pages 0
        // & 3, and write Test Unlock/Exit tokens to OTP secret0 partition.
        LOG_INFO("Performing all CP provisioning steps ...");
        CHECK_STATUS_OK(
            device_id_and_manuf_state_flash_info_page_erase(provisioning_data));
        CHECK_STATUS_OK(
            wafer_auth_secret_flash_info_page_erase(provisioning_data));
        CHECK_STATUS_OK(
            device_id_and_manuf_state_flash_info_page_write(provisioning_data));
        CHECK_STATUS_OK(
            wafer_auth_secret_flash_info_page_write(provisioning_data));
        CHECK_STATUS_OK(manuf_individualize_device_secret0(&lc_ctrl, &otp_ctrl,
                                                           provisioning_data));
        break;
      case kCpProvisioningCommandFlashInfoEraseDeviceIdAndManufState:
        LOG_INFO("Erasing device ID and manuf state flash info page ...");
        CHECK_STATUS_OK(
            device_id_and_manuf_state_flash_info_page_erase(provisioning_data));
        break;
      case kCpProvisioningCommandFlashInfoEraseWaferAuthSecret:
        LOG_INFO("Erasing wafer auth secret flash info page ...");
        CHECK_STATUS_OK(
            wafer_auth_secret_flash_info_page_erase(provisioning_data));
        break;
      case kCpProvisioningCommandFlashInfoWriteDeviceIdAndManufState:
        LOG_INFO("Writing device ID and manuf state flash info page ...");
        CHECK_STATUS_OK(
            device_id_and_manuf_state_flash_info_page_write(provisioning_data));
        break;
      case kCpProvisioningCommandFlashInfoWriteWaferAuthSecret:
        LOG_INFO("Writing wafer auth secret flash info page ...");
        CHECK_STATUS_OK(
            wafer_auth_secret_flash_info_page_write(provisioning_data));
        break;
      case kCpProvisioningCommandOtpSecret0WriteAndLock:
        LOG_INFO("Writing and locking OTP secret0 partition ...");
        CHECK_STATUS_OK(manuf_individualize_device_secret0(&lc_ctrl, &otp_ctrl,
                                                           provisioning_data));
        break;
      case kCpProvisioningCommandDone:
        LOG_INFO("CP provisioning done.");
        return RESP_OK_STATUS(uj);
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
    RESP_OK_STATUS(uj);
  }
  // We should never reach here.
  return INTERNAL();
}

bool sram_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Check we are in in TEST_UNLOCKED0.
  CHECK_STATUS_OK(
      lc_ctrl_testutils_check_lc_state(&lc_ctrl, kDifLcCtrlStateTestUnlocked0));

  LOG_INFO("Waiting for CP provisioning data ...");

  // Get provisioning data over console.
  manuf_cp_provisioning_data_t provisioning_data;
  CHECK_STATUS_OK(
      ujson_deserialize_manuf_cp_provisioning_data_t(&uj, &provisioning_data));

  // TODO(#19453): Provision AST configuration. This will most likely need to be
  // done before provisioning the test unlock/exit tokens below, as these write
  // to a scrambled (SECRET0) partition, which requires entropy.

  // Process provisioning commands.
  CHECK_STATUS_OK(command_processor(&uj, &provisioning_data));

  return true;
}
