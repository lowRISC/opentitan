// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/manuf/base/ft_device_id.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/nvm_info_field.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top/ast_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;

#ifndef ATE
static manuf_ft_individualize_data_t in_data;
#endif

// ATE Indicator GPIOs. Pin number of GPIO1.
static const dif_gpio_pin_t kGpioPinTestStart = 22;          // gpio1, IOR7
static const dif_gpio_pin_t kGpioPinTestDone = 28;           // gpio1, IOR13
static const dif_gpio_pin_t kGpioPinTestError = 27;          // gpio1, IOR12
static const dif_gpio_pin_t kGpioPinSpiConsoleTxReady = 25;  // gpio1, IOR10
static const dif_gpio_pin_t kGpioPinSpiConsoleRxReady = 26;  // gpio1, IOR11

#ifndef ATE
OTTF_DEFINE_TEST_CONFIG(
        .console.type = kOttfConsoleSpiDevice,
        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
        .console.test_may_clobber = false, .silence_console_prints = true,
        .console_tx_indicator.enable = true,
        .console_tx_indicator.spi_console_tx_ready_mio = kDtPadIor10,
        // The GPIO id is global, so skip the 32 gpio0 pins to reach gpio1.
        .console_tx_indicator.spi_console_tx_ready_gpio =
            kDifGpioNumPins + kGpioPinSpiConsoleTxReady);
#else
OTTF_DEFINE_TEST_CONFIG();
#endif

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO1_BASE_ADDR),
                    &gpio));
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
  // IOR11 / gpio1 pin 26 is for SPI console RX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIor11,
      kTopEarlgreyPinmuxOutselGpio1Gpio0 + kGpioPinSpiConsoleRxReady));
  // IOR10 / gpio1 pin 25 is for SPI console TX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIor10,
      kTopEarlgreyPinmuxOutselGpio1Gpio0 + kGpioPinSpiConsoleTxReady));
  // IOR12 / gpio1 pin 27 is for error reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIor12,
      kTopEarlgreyPinmuxOutselGpio1Gpio0 + kGpioPinTestError));
  // IOR13 / gpio1 pin 28 is for test done reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIor13,
      kTopEarlgreyPinmuxOutselGpio1Gpio0 + kGpioPinTestDone));
  // IOR7 / gpio1 pin 22 is for test start reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIor7,
      kTopEarlgreyPinmuxOutselGpio1Gpio0 + kGpioPinTestStart));
  TRY(dif_gpio_output_set_enabled_all(
      &gpio, (1u << kGpioPinTestStart) | (1u << kGpioPinTestDone) |
                 (1u << kGpioPinTestError) | (1u << kGpioPinSpiConsoleTxReady) |
                 (1u << kGpioPinSpiConsoleRxReady)));
  TRY(dif_gpio_write_all(&gpio, /*write_val=*/0));  // Initialize all to 0.
  return OK_STATUS();
}

/**
 * Patch AST config if patch exists in flash info page 0.
 */
static status_t patch_ast_config_value(void) {
  // Read patch address and value from flash info 0.
  uint32_t ast_patch_addr_offset;
  uint32_t ast_patch_value;
  TRY(nvm_testutils_info_page_setup(kNvmInfoFieldAstIndividPatchAddr.page,
                                    kPageReadOnly, kPageRawCfg));
  TRY(manuf_nvm_info_field_read(
      kNvmInfoFieldAstIndividPatchAddr, &ast_patch_addr_offset,
      kNvmInfoFieldAstIndividPatchAddrSizeIn32BitWords));
  TRY(manuf_nvm_info_field_read(
      kNvmInfoFieldAstIndividPatchVal, &ast_patch_value,
      kNvmInfoFieldAstIndividPatchValSizeIn32BitWords));

  // Read the CRC32 that wafer-test equipment should have written alongside
  // the two fields above, if a patch is present. If it doesn't match, treat
  // the patch as absent.
  uint32_t ast_patch_crc;
  static_assert(kNvmInfoFieldAstIndividPatchCrcSizeIn32BitWords == 1,
                "AST patch CRC should fit in <32bits.");
  TRY(manuf_nvm_info_field_read(
      kNvmInfoFieldAstIndividPatchCrc, &ast_patch_crc,
      kNvmInfoFieldAstIndividPatchCrcSizeIn32BitWords));
  const uint32_t ast_patch_words[] = {ast_patch_addr_offset, ast_patch_value};
  if (crc32(ast_patch_words, sizeof(ast_patch_words)) != ast_patch_crc) {
    ast_patch_value = 0;
  }

  // Only patch AST if the patch value is present.
  if (ast_patch_value != 0 && ast_patch_value != UINT32_MAX) {
    // Check the address is within range before programming.
    TRY_CHECK(ast_patch_addr_offset * sizeof(uint32_t) <= AST_REGAL_REG_OFFSET,
              "AST patch address offset out of range.");
    // Write patch value.
    abs_mmio_write32(
        TOP_EARLGREY_AST_BASE_ADDR + ast_patch_addr_offset * sizeof(uint32_t),
        ast_patch_value);
  }

  return OK_STATUS();
}

/**
 * Provisions the (default) boot data explicitly.
 *
 * This function is used to ensure the perso is bootable when the
 * `DEFAULT_BOOT_DATA_IN_PROD_EN` OTP is disabled. This is done by
 * explicitly provisioning the default boot data. This function is a
 * no-op if any boot data has already been provisioned.
 */
static status_t provision_boot_data(void) {
  boot_data_t boot_data;
  TRY(boot_data_read(kLcStateTest, &boot_data));
  TRY(boot_data_write(&boot_data));
  return OK_STATUS();
}

/**
 * Provision OTP {CreatorSw,OwnerSw,Hw}Cfg and RotCreatorAuth{Codesign,State}
 * partitions.
 *
 * Note: CreatorSwCfg and OwnerSwCfg partitions are not locked yet, as not
 * all fields can be programmed until the personalization stage.
 */
static status_t provision(ujson_t *uj) {
  // Patch AST config if requested.
  TRY(patch_ast_config_value());

  // Perform OTP writes.
#ifndef ATE
  // Get host data.
  base_printf("Waiting for FT SRAM provisioning data ...\r\n");
  TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, true));
  TRY(ujson_deserialize_manuf_ft_individualize_data_t(uj, &in_data));
  TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, false));
  TRY(manuf_individualize_device_hw_cfg(&otp_ctrl, in_data.ft_device_id));
#else
  TRY(manuf_individualize_device_hw_cfg(&otp_ctrl, kFtDeviceId));
#endif
  TRY(manuf_individualize_device_rot_creator_auth_codesign(&otp_ctrl));
  TRY(manuf_individualize_device_rot_creator_auth_state(&otp_ctrl));
  TRY(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
  TRY(manuf_individualize_device_creator_sw_cfg(&otp_ctrl));
  TRY(provision_boot_data());

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(entropy_complex_init(kHardenedBoolFalse));
  CHECK_STATUS_OK(configure_ate_gpio_indicators());
  ujson_t uj;
#ifndef ATE
  ottf_console_init();
  uj = ujson_ottf_console();
#endif

  // Perform provisioning operations.
  CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestStart, true));
  status_t result = provision(&uj);
  if (!status_ok(result)) {
    CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestError, true));
  } else {
    CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestDone, true));
  }
  return true;
}
