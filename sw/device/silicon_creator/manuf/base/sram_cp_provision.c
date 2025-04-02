// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
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
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;

static uint32_t ast_cfg_data[kFlashInfoAstCalibrationDataSizeIn32BitWords];

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));
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

static status_t flash_info_page_0_read_and_validate(
    manuf_cp_provisioning_data_out_t *console_out) {
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldCpDeviceId.page,
      kFlashInfoFieldCpDeviceId.bank, kFlashInfoFieldCpDeviceId.partition,
      kFlashInfoPage0Permissions, /*offset=*/NULL));

  // Read (wafer) lot name.
  uint32_t lot_name = 0;
  static_assert(kFlashInfoFieldLotNameSizeIn32BitWords == 1,
                "Lot name should fit in <32bits.");
  TRY(manuf_flash_info_field_read(&flash_ctrl_state, kFlashInfoFieldLotName,
                                  &lot_name,
                                  kFlashInfoFieldLotNameSizeIn32BitWords));

  // Read wafer number.
  uint32_t wafer_number = 0;
  static_assert(kFlashInfoFieldWaferNumberSizeIn32BitWords == 1,
                "Wafer number should fit in <32bits.");
  TRY(manuf_flash_info_field_read(&flash_ctrl_state, kFlashInfoFieldWaferNumber,
                                  &wafer_number,
                                  kFlashInfoFieldWaferNumberSizeIn32BitWords));

  // Read wafer X coord.
  uint32_t wafer_x_coord = 0;
  static_assert(kFlashInfoFieldWaferXCoordSizeIn32BitWords == 1,
                "Wafer X coordinate value should fit in <32bits.");
  TRY(manuf_flash_info_field_read(&flash_ctrl_state, kFlashInfoFieldWaferXCoord,
                                  &wafer_x_coord,
                                  kFlashInfoFieldWaferXCoordSizeIn32BitWords));

  // Read wafer Y coord.
  uint32_t wafer_y_coord = 0;
  static_assert(kFlashInfoFieldWaferYCoordSizeIn32BitWords == 1,
                "Wafer Y coordinate value should fit in <32bits.");
  TRY(manuf_flash_info_field_read(&flash_ctrl_state, kFlashInfoFieldWaferYCoord,
                                  &wafer_y_coord,
                                  kFlashInfoFieldWaferYCoordSizeIn32BitWords));

  // Read AST calibration values into RAM.
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldAstCalibrationData, ast_cfg_data,
      kFlashInfoAstCalibrationDataSizeIn32BitWords));

  // Encode CP device ID.
  // HW origin portion of CP device.
  // "0x00024001" encodes:
  //   - a SiliconCreator ID of "0x4001" for "Nuvoton", and
  //   - a Product ID of "0x0002" for Earlgrey A1 silicon.
  console_out->cp_device_id[0] = 0x00024001u;
  // Device Identification Number portion of CP device ID.
  uint32_t year = (lot_name >> 24) & 0xf;
  uint32_t week = (lot_name >> 16) & 0xff;
  uint32_t lot_number = lot_name & 0xfff;
  console_out->cp_device_id[1] =
      (wafer_number << 24) | (lot_number << 12) | (week << 4) | year;
  console_out->cp_device_id[2] = (wafer_y_coord << 12) | wafer_x_coord;
  // Reserved word; set to 0.
  console_out->cp_device_id[3] = 0;

  // Write CP device ID.
  TRY(manuf_flash_info_field_write(&flash_ctrl_state, kFlashInfoFieldCpDeviceId,
                                   console_out->cp_device_id,
                                   kFlashInfoFieldCpDeviceIdSizeIn32BitWords,
                                   /*erase_page_before_write=*/false));

  return OK_STATUS();
}

static status_t wafer_auth_secret_flash_info_page_write(
    manuf_cp_provisioning_data_t *console_in) {
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret.page,
      kFlashInfoFieldWaferAuthSecret.bank,
      kFlashInfoFieldWaferAuthSecret.partition, kFlashInfoPage3WritePermissions,
      /*offset=*/NULL));
  TRY(manuf_flash_info_field_write(
      &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret,
      console_in->wafer_auth_secret,
      kFlashInfoFieldWaferAuthSecretSizeIn32BitWords,
      /*erase_page_before_write=*/true));
  return OK_STATUS();
}

static status_t print_inputs_to_console(
    manuf_cp_provisioning_data_t *console_in) {
  uint32_t high;
  uint32_t low;

  LOG_INFO("Test Unlock Token Hash:");
  for (size_t i = 0; i < ARRAYSIZE(console_in->test_unlock_token_hash); ++i) {
    high = console_in->test_unlock_token_hash[i] >> 32;
    low = console_in->test_unlock_token_hash[i] & 0xffffffff;
    LOG_INFO("0x%08x%08x", high, low);
  }
  LOG_INFO("Test Exit Token Hash:");
  for (size_t i = 0; i < ARRAYSIZE(console_in->test_exit_token_hash); ++i) {
    high = console_in->test_exit_token_hash[i] >> 32;
    low = console_in->test_exit_token_hash[i] & 0xffffffff;
    LOG_INFO("0x%08x%08x", high, low);
  }
  return OK_STATUS();
}

/**
 * Provision flash info pages 0 and 3, and OTP Secret0 partition.
 */
static status_t provision(ujson_t *uj,
                          manuf_cp_provisioning_data_out_t *console_out) {
  // Wait for input console data.
  LOG_INFO("Waiting for CP provisioning data ...");
  manuf_cp_provisioning_data_t console_in;
  TRY(ujson_deserialize_manuf_cp_provisioning_data_t(uj, &console_in));
  TRY(print_inputs_to_console(&console_in));

  // Provision flash info page 3 (wafer authentication secret).
  TRY(wafer_auth_secret_flash_info_page_write(&console_in));

  // Burn test tokens into OTP.
  TRY(manuf_individualize_device_secret0(&lc_ctrl, &otp_ctrl, &console_in));

  // Send data back to host.
  LOG_INFO("Exporting CP device ID ...");
  RESP_OK(ujson_serialize_manuf_cp_provisioning_data_out_t, uj, console_out);

  return OK_STATUS();
}

bool test_main(void) {
  // Initialize DIF handles, pinmux, and console.
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Extract factory data from flash info page 0.
  manuf_cp_provisioning_data_out_t console_out;
  CHECK_STATUS_OK(flash_ctrl_testutils_wait_for_init(&flash_ctrl_state));
  CHECK_STATUS_OK(flash_info_page_0_read_and_validate(&console_out));

  // Initialize AST.
  manually_init_ast(ast_cfg_data);
  LOG_INFO("AST manually configured.");

  // Perform CP provisioning operations.
  CHECK_STATUS_OK(provision(&uj, &console_out));

  LOG_INFO("CP provisioning done.");
  return true;
}
