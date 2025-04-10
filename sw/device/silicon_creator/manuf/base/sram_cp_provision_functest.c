// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
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
#include "sw/device/silicon_creator/manuf/base/cp_device_id.h"
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

/**
 * Writes test data to flash info page 0 so the sram_cp_provision.c program can
 * read it out.
 */
static status_t prep_flash_info_page_0(manuf_cp_test_data_t *test_data) {
  // Setup page permissions on flash info page 0.
  uint32_t byte_address = 0;
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldCpDeviceId.page,
      kFlashInfoFieldCpDeviceId.bank, kFlashInfoFieldCpDeviceId.partition,
      kFlashInfoPage0Permissions, &byte_address));

  // Lot name.
  TRY(manuf_flash_info_field_write(&flash_ctrl_state, kFlashInfoFieldLotName,
                                   &test_data->lot_name,
                                   kFlashInfoFieldLotNameSizeIn32BitWords,
                                   /*erase_page_before_write=*/true));

  // Wafer number.
  TRY(manuf_flash_info_field_write(
      &flash_ctrl_state, kFlashInfoFieldWaferNumber, &test_data->wafer_number,
      kFlashInfoFieldWaferNumberSizeIn32BitWords,
      /*erase_page_before_write=*/false));

  // Wafer X coord.
  TRY(manuf_flash_info_field_write(
      &flash_ctrl_state, kFlashInfoFieldWaferXCoord, &test_data->wafer_x_coord,
      kFlashInfoFieldWaferXCoordSizeIn32BitWords,
      /*erase_page_before_write=*/false));

  // Wafer Y coord.
  TRY(manuf_flash_info_field_write(
      &flash_ctrl_state, kFlashInfoFieldWaferYCoord, &test_data->wafer_y_coord,
      kFlashInfoFieldWaferYCoordSizeIn32BitWords,
      /*erase_page_before_write=*/false));

  return OK_STATUS();
}

bool test_main(void) {
  // Initialize peripherals, pinmux, and console.
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Get LC state.
  dif_lc_ctrl_state_t lc_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));

  // Get CP test data over console.
  LOG_INFO("Waiting for CP test data ...");
  manuf_cp_test_data_t test_data;
  CHECK_STATUS_OK(ujson_deserialize_manuf_cp_test_data_t(&uj, &test_data));

  if (lc_state == kDifLcCtrlStateTestUnlocked0) {
    // Write test data to flash info page 0.
    CHECK_STATUS_OK(prep_flash_info_page_0(&test_data));
    LOG_INFO("Flash info page 0 programmed.");
  } else if (lc_state == kDifLcCtrlStateTestUnlocked1) {
    // Read and validate CP device ID.
    uint32_t cp_device_id[kFlashInfoFieldCpDeviceIdSizeIn32BitWords] = {0};
    static_assert(kFlashInfoFieldCpDeviceIdSizeIn32BitWords == 4,
                  "CP device ID should fit in four 32bit words.");
    CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup_properties(
        &flash_ctrl_state, kFlashInfoFieldCpDeviceId.page,
        kFlashInfoFieldCpDeviceId.bank, kFlashInfoFieldCpDeviceId.partition,
        kFlashInfoPage0Permissions, /*offset=*/NULL));
    CHECK_STATUS_OK(manuf_flash_info_field_read(
        &flash_ctrl_state, kFlashInfoFieldCpDeviceId, cp_device_id,
        kFlashInfoFieldCpDeviceIdSizeIn32BitWords));
    uint32_t year = (test_data.lot_name >> 24) & 0xf;
    uint32_t week = (test_data.lot_name >> 16) & 0xff;
    uint32_t lot_number = test_data.lot_name & 0xfff;
    CHECK(cp_device_id[0] == kCpDeviceId[0]);
    CHECK(cp_device_id[1] == ((test_data.wafer_number << 24) |
                              (lot_number << 12) | (week << 4) | year));
    CHECK(cp_device_id[2] ==
          ((test_data.wafer_y_coord << 12) | test_data.wafer_x_coord));
    CHECK(cp_device_id[3] == 0);

    // Note: we cannot read/check the wafer_auth_secret field in flash info page
    // 3, as this page is not readable in the TEST_UNLOCKED* states.

    // Check the secret0 partition has been provisioned / locked.
    CHECK_STATUS_OK(manuf_individualize_device_secret0_check(&otp_ctrl));
    LOG_INFO("Checks complete. Success");
  } else {
    LOG_INFO("Bad LC state.");
    return false;
  }

  return true;
}
