// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifndef AST_PROGRAM_UNITTEST
// In normal operation, AST writes should go directly to the AST
// peripheral.  The DIF variables should be only visible to this
// source unit.
#define ast_write(addr, data) abs_mmio_write32(addr, data)
static dif_flash_ctrl_state_t flash_state;
static dif_pinmux_t pinmux;
static dif_uart_t uart0;
#else
// If we're running a unit test, we want to supply an AST writing function
// and make the DIFs externally visible so the test program can verify
// the written values and examine/modify the flash.
extern void ast_write(uint32_t addr, uint32_t data);
dif_flash_ctrl_state_t flash_state;
dif_pinmux_t pinmux;
dif_uart_t uart0;
#endif

static status_t setup_uart(bool enable) {
  if (enable) {
    TRY(dif_pinmux_init(
        mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
    TRY(dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInUart0Rx,
                                kTopEarlgreyPinmuxInselIoc3));
    TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc3,
                                 kTopEarlgreyPinmuxOutselConstantHighZ));
    TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc4,
                                 kTopEarlgreyPinmuxOutselUart0Tx));
    TRY(dif_uart_init(mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
                      &uart0));
    TRY(dif_uart_configure(&uart0,
                           (dif_uart_config_t){
                               .baudrate = (uint32_t)kUartBaudrate,
                               .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                               .parity_enable = kDifToggleDisabled,
                               .parity = kDifUartParityEven,
                               .tx_enable = kDifToggleEnabled,
                               .rx_enable = kDifToggleEnabled,
                           }));
    base_uart_stdout(&uart0);
  } else {
    base_uart_stdout(NULL);
  }
  return OK_STATUS();
}

status_t ast_program_init(bool verbose) {
  setup_uart(verbose);
  LOG_INFO("Starting AST config");
  // Initialize the flash_ctrl DIF.
  TRY(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(flash_ctrl_testutils_wait_for_init(&flash_state));

  // Set up parameters for accessing the AST calibration data in flash info page
  // 0.
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

  return OK_STATUS();
}

status_t ast_program_config(bool verbose) {
  TRY(ast_program_init(verbose));

  // Read AST calibration values from flash.
  LOG_INFO("Reading AST data");
  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      (kFlashInfoFieldAstCalibrationData.page * device_info.bytes_per_page) +
      kFlashInfoFieldAstCalibrationData.byte_offset;
  uint32_t ast_data[kFlashInfoAstCalibrationDataSizeIn32BitWords];
  TRY(flash_ctrl_testutils_wait_for_init(&flash_state));
  TRY(flash_ctrl_testutils_read(&flash_state, byte_address,
                                kFlashInfoFieldAstCalibrationData.partition,
                                ast_data, kDifFlashCtrlPartitionTypeInfo,
                                kFlashInfoAstCalibrationDataSizeIn32BitWords,
                                /*delay=*/0));

  // Program AST CSRs.
  LOG_INFO("Programming %u AST words",
           kFlashInfoAstCalibrationDataSizeIn32BitWords);
  for (size_t i = 0; i < kFlashInfoAstCalibrationDataSizeIn32BitWords; ++i) {
    uint32_t addr = TOP_EARLGREY_AST_BASE_ADDR + i * sizeof(uint32_t);
    uint32_t data = ast_data[i];
    LOG_INFO("\tAddress = 0x%08x, Data = 0x%08x", addr, data);
    ast_write(addr, data);
  }

  return OK_STATUS();
}
