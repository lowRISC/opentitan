// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_pinmux_t pinmux;
static dif_flash_ctrl_state_t flash_state;
static dif_uart_t uart;

// ---------------------------------------------------------------------------
// Enter Calibration Values for Specific Chip Here:
// ---------------------------------------------------------------------------
enum {
  kNumCalibrationWords = 8,
};
const uint32_t kAstCfgData[kNumCalibrationWords] = {
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
};
uint32_t kAstCfgAddrs[kNumCalibrationWords] = {
    0x0, 0x4, 0x8, 0xc, 0x10, 0x14, 0x18, 0x1c,
};
// ---------------------------------------------------------------------------

static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  TRY(dif_uart_init(mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
                    &uart));
  return OK_STATUS();
}

static status_t init_uart(void) {
  TRY_CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  TRY_CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
            "kClockFreqPeripheralHz must fit in uint32_t");
  TRY(dif_uart_configure(&uart,
                         (dif_uart_config_t){
                             .baudrate = (uint32_t)kUartBaudrate,
                             .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                             .parity_enable = kDifToggleDisabled,
                             .parity = kDifUartParityEven,
                             .tx_enable = kDifToggleEnabled,
                             .rx_enable = kDifToggleEnabled,
                         }));
  base_uart_stdout(&uart);
  return OK_STATUS();
}

static void manually_init_ast(void) {
  for (size_t i = 0; i < kNumCalibrationWords; ++i) {
    abs_mmio_write32(TOP_EARLGREY_AST_BASE_ADDR + kAstCfgAddrs[i],
                     kAstCfgData[i]);
  }
}

static status_t write_ast_values_to_flash(void) {
  // Prepase AST calibration data buffer.
  uint32_t ast_cfgs[(kNumCalibrationWords * 2) + 1];
  ast_cfgs[0] = kNumCalibrationWords;
  for (size_t i = 0; i < kNumCalibrationWords; ++i) {
    ast_cfgs[i * 2 + 1] = kAstCfgAddrs[i] + TOP_EARLGREY_AST_BASE_ADDR;
    ast_cfgs[i * 2 + 2] = kAstCfgData[i];
  }

  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_state, kFlashInfoFieldAstCalibrationData.page,
      kFlashInfoFieldAstCalibrationData.bank,
      kFlashInfoFieldAstCalibrationData.partition,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4True,
          .prog_en = kMultiBitBool4True,
          .rd_en = kMultiBitBool4True,
          .scramble_en = kMultiBitBool4False},
      /*offset=*/NULL));
  TRY(manuf_flash_info_field_write(&flash_state,
                                   kFlashInfoFieldAstCalibrationData, ast_cfgs,
                                   (kNumCalibrationWords * 2) + 1,
                                   /*erase_page_before_write=*/true));

  return OK_STATUS();
}

void sram_main(void) {
  // Initialize AST, DIF handles, pinmux, and UART.
  manually_init_ast();
  peripheral_handles_init();
  pinmux_testutils_init(&pinmux);
  CHECK_STATUS_OK(init_uart());
  LOG_INFO("AST manually configured.");

  // Write AST calibration values to flash info page 0.
  CHECK_STATUS_OK(write_ast_values_to_flash());
  LOG_INFO("AST calibration values written to flash info page 0.");

  test_status_set(kTestStatusPassed);
}
