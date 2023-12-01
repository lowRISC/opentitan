// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifndef AST_PROGRAM_UNITTEST
// In normal operation, AST writes should go directly to the AST
// peripheral.  The DIF variables should be only visible to this
// source unit.
#define ast_write(addr, data) abs_mmio_write32(addr, data)
static dif_flash_ctrl_state_t flash_state;
static dif_uart_t uart0;
#else
// If we're running a unit test, we want to supply an AST writing function
// and make the DIFs externally visible so the test program can verify
// the written values and examine/modify the flash.
extern void ast_write(uint32_t addr, uint32_t data);
dif_flash_ctrl_state_t flash_state;
dif_uart_t uart0;
#endif

static status_t setup_uart(bool enable) {
  if (enable) {
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

  // Set up parameters for accessing the AST calibration data in flash info page
  // 0.
  dif_flash_ctrl_info_region_t info_region = {
      .bank = kFlashInfoFieldAstCalibrationData.bank,
      .page = kFlashInfoFieldAstCalibrationData.page,
      .partition_id = kFlashInfoFieldAstCalibrationData.partition};

  dif_flash_ctrl_region_properties_t kFlashInfoPage0Permissions = {
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False,
      .erase_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False};

  TRY(dif_flash_ctrl_set_info_region_properties(&flash_state, info_region,
                                                kFlashInfoPage0Permissions));
  TRY(dif_flash_ctrl_set_info_region_enablement(&flash_state, info_region,
                                                kDifToggleEnabled));
  return OK_STATUS();
}

status_t ast_program_config(bool verbose) {
  TRY(ast_program_init(verbose));
  LOG_INFO("Reading AST data");
  // Prepare the read transaction.
  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      (kFlashInfoFieldAstCalibrationData.page * device_info.bytes_per_page) +
      kFlashInfoFieldAstCalibrationData.byte_offset;
  dif_flash_ctrl_transaction_t transaction = {
      .byte_address = byte_address,
      .op = kDifFlashCtrlOpRead,
      .partition_type = kDifFlashCtrlPartitionTypeInfo,
      .partition_id = kFlashInfoFieldAstCalibrationData.partition,
      .word_count = kFlashInfoFieldMaxAstCalibrationDataSizeIn32BitWords};
  // Read the data.
  TRY(dif_flash_ctrl_start(&flash_state, transaction));
  uint32_t ast_data[kFlashInfoFieldMaxAstCalibrationDataSizeIn32BitWords];
  TRY(dif_flash_ctrl_read_fifo_pop(&flash_state, transaction.word_count,
                                   ast_data));
  dif_flash_ctrl_output_t output;
  TRY(dif_flash_ctrl_end(&flash_state, &output));

  // Program AST
  // The form of the AST data is: <count> [<address> <data> ...]
  if (ast_data[0] < kFlashInfoFieldMaxAstCalibrationDataSizeIn32BitWords / 2) {
    LOG_INFO("Programming %u AST words", ast_data[0]);
    for (size_t i = 0; i < ast_data[0]; ++i) {
      uint32_t addr = ast_data[1 + i * 2];
      uint32_t data = ast_data[2 + i * 2];
      ast_write(addr, data);
    }
  } else {
    LOG_ERROR("AST data error: length %u >= %u", ast_data[0],
              kFlashInfoFieldMaxAstCalibrationDataSizeIn32BitWords / 2);
    return UNKNOWN();
  }
  return OK_STATUS();
}
