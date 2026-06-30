// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/base/cp_device_id.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/nvm_info_field.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const dif_gpio_pin_t kGpioPinSpiConsoleTxReady = 0;

OTTF_DEFINE_TEST_CONFIG(
        .console.type = kOttfConsoleSpiDevice,
        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
        .console.test_may_clobber = false, .silence_console_prints = true,
        .console_tx_indicator.enable = true,
        .console_tx_indicator.spi_console_tx_ready_mio = kDtPadIoa5,
        .console_tx_indicator.spi_console_tx_ready_gpio =
            kGpioPinSpiConsoleTxReady);

static dif_gpio_t gpio;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  TRY(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR),
                      &pinmux));
  return OK_STATUS();
}

/**
 * Configure the ATE GPIO indicator pins.
 */
static status_t configure_ate_gpio_indicators(void) {
  // IOA5 / GPIO0 is for SPI console TX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa5,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinSpiConsoleTxReady));
  TRY(dif_gpio_output_set_enabled_all(&gpio, 0x1));  // Enable first GPIO.
  TRY(dif_gpio_write_all(&gpio, /*write_val=*/0));   // Intialize all to 0.
  return OK_STATUS();
}

/**
 * Writes test data to flash info page 0 so the sram_cp_provision.c program can
 * read it out.
 */
static status_t prep_flash_info_page_0(manuf_cp_test_data_t *test_data) {
  TRY(nvm_testutils_info_page_setup(kNvmInfoFieldLotName.page, kPageReadWrite,
                                    kPageRawCfg));
  // Lot name.
  TRY(manuf_nvm_info_field_write(kNvmInfoFieldLotName, &test_data->lot_name,
                                 kNvmInfoFieldLotNameSizeIn32BitWords,
                                 /*erase_page_before_write=*/true,
                                 /*readback=*/true));

  // Wafer number.
  TRY(manuf_nvm_info_field_write(kNvmInfoFieldWaferNumber,
                                 &test_data->wafer_number,
                                 kNvmInfoFieldWaferNumberSizeIn32BitWords,
                                 /*erase_page_before_write=*/false,
                                 /*readback=*/true));

  // Wafer X coord.
  TRY(manuf_nvm_info_field_write(kNvmInfoFieldWaferXCoord,
                                 &test_data->wafer_x_coord,
                                 kNvmInfoFieldWaferXCoordSizeIn32BitWords,
                                 /*erase_page_before_write=*/false,
                                 /*readback=*/true));

  // Wafer Y coord.
  TRY(manuf_nvm_info_field_write(kNvmInfoFieldWaferYCoord,
                                 &test_data->wafer_y_coord,
                                 kNvmInfoFieldWaferYCoordSizeIn32BitWords,
                                 /*erase_page_before_write=*/false,
                                 /*readback=*/true));

  return OK_STATUS();
}

bool test_main(void) {
  // Initialize peripherals, pinmux, and console.
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init(kHardenedBoolFalse));
  CHECK_STATUS_OK(configure_ate_gpio_indicators());
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Get LC state.
  dif_lc_ctrl_state_t lc_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));

  // Get CP test data over console.
  base_printf("Waiting for CP test data ...\n");
  manuf_cp_test_data_t test_data;
  CHECK_STATUS_OK(ujson_deserialize_manuf_cp_test_data_t(&uj, &test_data));

  if (lc_state == kDifLcCtrlStateTestUnlocked0) {
    // Write test data to flash info page 0.
    CHECK_STATUS_OK(prep_flash_info_page_0(&test_data));
    base_printf("Flash info page 0 programmed.\n");
  } else if (lc_state == kDifLcCtrlStateTestUnlocked1) {
    // Read and validate CP device ID.
    uint32_t cp_device_id[kNvmInfoFieldCpDeviceIdSizeIn32BitWords] = {0};
    static_assert(kNvmInfoFieldCpDeviceIdSizeIn32BitWords == 4,
                  "CP device ID should fit in four 32bit words.");
    CHECK_STATUS_OK(nvm_testutils_info_page_setup(kNvmInfoFieldCpDeviceId.page,
                                                  kPageReadOnly, kPageRawCfg));
    CHECK_STATUS_OK(
        manuf_nvm_info_field_read(kNvmInfoFieldCpDeviceId, cp_device_id,
                                  kNvmInfoFieldCpDeviceIdSizeIn32BitWords));
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
    base_printf("Checks complete. Success.\n");
  } else {
    base_printf("Bad LC state.\n");
    return false;
  }

  return true;
}
