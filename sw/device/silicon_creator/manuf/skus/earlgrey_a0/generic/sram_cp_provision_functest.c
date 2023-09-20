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

static status_t check_device_id_and_manuf_state(
    manuf_cp_provisioning_data_t *expected_data) {
  LOG_INFO("Checking expected DeviceId and ManufState data ...");
  // Configure flash info page 0 permissions.
  uint32_t byte_address = 0;
  uint32_t actual_device_id[kHwCfgDeviceIdSizeIn32BitWords] = {0};
  uint32_t actual_manuf_state[kHwCfgManufStateSizeIn32BitWords] = {0};
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldDeviceId.page,
      kFlashInfoFieldDeviceId.bank, kFlashInfoFieldDeviceId.partition,
      kFlashInfoPage0Permissions, &byte_address));

  // Read and check device_id.
  TRY(flash_ctrl_testutils_read(
      &flash_ctrl_state, byte_address, kFlashInfoFieldDeviceId.partition,
      actual_device_id, kDifFlashCtrlPartitionTypeInfo,
      kHwCfgDeviceIdSizeIn32BitWords,
      /*delay_micros=*/0));
  CHECK_ARRAYS_EQ(actual_device_id, expected_data->device_id,
                  kHwCfgDeviceIdSizeIn32BitWords);

  // Read and check manuf_state (on same page as device_id).
  TRY(flash_ctrl_testutils_read(
      &flash_ctrl_state, byte_address + kFlashInfoFieldManufState.byte_offset,
      kFlashInfoFieldManufState.partition, actual_manuf_state,
      kDifFlashCtrlPartitionTypeInfo, kHwCfgManufStateSizeIn32BitWords,
      /*delay_micros=*/0));
  CHECK_ARRAYS_EQ(actual_manuf_state, expected_data->manuf_state,
                  kHwCfgManufStateSizeIn32BitWords);

  return OK_STATUS();
}

bool sram_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Check we are in in TEST_UNLOCKED1.
  CHECK_STATUS_OK(
      lc_ctrl_testutils_check_lc_state(&lc_ctrl, kDifLcCtrlStateTestUnlocked1));

  LOG_INFO("Waiting for expected CP provisioning data ...");

  // Get expected provisioning data over console.
  manuf_cp_provisioning_data_t expected_data;
  CHECK_STATUS_OK(
      ujson_deserialize_manuf_cp_provisioning_data_t(&uj, &expected_data));

  // Read and check device_id and manuf_state fields from flash info page 0.
  CHECK_STATUS_OK(check_device_id_and_manuf_state(&expected_data));

  // Note: we cannot read/check the wafer_auth_secret field in flash info page
  // 3, as this page is not readable in the TEST_UNLOCKED* states.

  // Check the secret0 partition has been provisioned / locked.
  CHECK_STATUS_OK(manuf_individualize_device_secret0_check(&otp_ctrl));

  LOG_INFO("Checks complete. Success");

  return true;
}
