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

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;

enum {
  /**
   * Number of flash info fields to provision.
   */
  kNumFlashInfoFields = 3,

  /**
   * Number of OTP fields to provision.
   */
  kNumOtpFields = 2,
};

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

static status_t write_flash_info_fields(
    manuf_cp_provisioning_data_t *provisioning_data) {
  const flash_info_field_t fields[kNumFlashInfoFields] = {
      kFlashInfoFieldDeviceId, kFlashInfoFieldManufState,
      kFlashInfoFieldWaferAuthSecret};
  const uint32_t *data[kNumFlashInfoFields] = {
      provisioning_data->device_id, provisioning_data->manuf_state,
      provisioning_data->wafer_auth_secret};
  const uint32_t data_sizes[kNumFlashInfoFields] = {
      kHwCfgDeviceIdSizeIn32BitWords, kHwCfgManufStateSizeIn32BitWords,
      kFlashInfoWaferAuthSecretSizeIn32BitWords};
  uint32_t byte_address;

  for (size_t i = 0; i < ARRAYSIZE(fields); ++i) {
    byte_address = 0;
    TRY(flash_ctrl_testutils_info_region_setup(
        &flash_ctrl_state, fields[i].page, fields[i].bank, fields[i].partition,
        &byte_address));
    // We skip the erasing of the ManufState (at index 1 in the arrays above)
    // field page as this field shares a page with the DeviceId field.
    if (i == 1) {
      TRY(flash_ctrl_testutils_write(
          &flash_ctrl_state, byte_address, fields[i].partition, data[i],
          kDifFlashCtrlPartitionTypeInfo, data_sizes[i]));
    } else {
      TRY(flash_ctrl_testutils_erase_and_write_page(
          &flash_ctrl_state, byte_address, fields[i].partition, data[i],
          kDifFlashCtrlPartitionTypeInfo, data_sizes[i]));
    }
  }

  return OK_STATUS();
}

bool sram_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Check we are in in TEST_UNLOCKED0.
  CHECK_STATUS_OK(
      lc_ctrl_testutils_check_lc_state(&lc_ctrl, kDifLcCtrlStateTestUnlocked0));

  LOG_INFO("CP provisioning start.");

  // Get provisioning data over console.
  manuf_cp_provisioning_data_t provisioning_data;
  CHECK_STATUS_OK(
      ujson_deserialize_manuf_cp_provisioning_data_t(&uj, &provisioning_data));

  // TODO(#19453): Provision AST configuration. This will most likely need to be
  // done before provisioning the test unlock/exit tokens below, as these write
  // to a scrambled (SECRET0) partition, which requires entropy.

  // Write DeviceId, ManufState, & WaferAuthSecret to flash info pages 0 & 3.
  CHECK_STATUS_OK(write_flash_info_fields(&provisioning_data));

  // Write Test Unlock/Exit tokens to OTP.
  CHECK_STATUS_OK(manuf_individualize_device_secret0(&lc_ctrl, &otp_ctrl,
                                                     &provisioning_data));

  LOG_INFO("CP provisioning end.");

  return true;
}
