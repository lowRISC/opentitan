// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "otp_img_stage_individualize.h"  // Generated.
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/flash_ctrl/dif/dif_flash_ctrl.h"
#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/lc_ctrl/driver/lc_ctrl.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/otp_ctrl/driver/otp_ctrl.h"
#include "sw/ip/otp_ctrl/test/utils/otp_ctrl_testutils.h"
#include "sw/ip/pinmux/driver/pinmux.h"
#include "sw/ip/pinmux/test/utils/pinmux_testutils.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/ip/uart/driver/uart.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/runtime/print.h"
#include "sw/lib/sw/device/silicon_creator/manuf/individualize_preop.h"
#include "sw/lib/sw/device/silicon_creator/manuf/isolated_flash_partition.h"
#include "sw/lib/sw/device/silicon_creator/manuf/otp_img.h"
#include "sw/lib/sw/device/silicon_creator/manuf/test_wafer_auth_secret.h"

#include "otp_ctrl_regs.h"  // Generated.

static dif_uart_t uart;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state, mmio_region_from_addr(kFlashCtrlCoreBaseAddr[0])));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(kLcCtrlRegsBaseAddr[0]),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(mmio_region_from_addr(kOtpCtrlCoreBaseAddr[0]),
                        &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(kPinmuxAonBaseAddr[0]), &pinmux));
  TRY(dif_uart_init(mmio_region_from_addr(kUartBaseAddr[0]), &uart));
  return OK_STATUS();
}

bool sram_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());

  // Initialize UART (for console, since we do not have the OTTF).
  pinmux_testutils_init(&pinmux);

  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                 .parity_enable = kDifToggleDisabled,
                 .parity = kDifUartParityEven,
                 .tx_enable = kDifToggleEnabled,
                 .rx_enable = kDifToggleEnabled,
             }));
  base_uart_stdout(&uart);

  LOG_INFO("Executing from SRAM.");

  // Read LC state.
  dif_lc_ctrl_state_t lc_state = kDifLcCtrlStateInvalid;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));

  uint32_t actual_wafer_auth_secret[kWaferAuthSecretSizeInWords] = {0};

  switch (lc_state) {
    case kDifLcCtrlStateTestUnlocked0:
    case kDifLcCtrlStateTestUnlocked1:
    case kDifLcCtrlStateTestUnlocked2:
    case kDifLcCtrlStateTestUnlocked3:
    case kDifLcCtrlStateTestUnlocked4:
    case kDifLcCtrlStateTestUnlocked5:
    case kDifLcCtrlStateTestUnlocked6:
    case kDifLcCtrlStateTestUnlocked7:
      LOG_INFO("Writing to the isolated flash partition.");
      CHECK_STATUS_OK(isolated_flash_partition_write(
          &flash_ctrl_state, kExpectedWaferAuthSecret,
          kWaferAuthSecretSizeInWords));
      LOG_INFO("Attempting to read back what was written.");
      CHECK_STATUS_NOT_OK(isolated_flash_partition_read(
          &flash_ctrl_state, kWaferAuthSecretSizeInWords,
          actual_wafer_auth_secret));
      LOG_INFO("Enabling ROM execution to enable bootstrap after reset.");
      CHECK_STATUS_OK(individualize_preop_otp_write(&otp_ctrl));
      LOG_INFO("Done. Perform an LC transition and run flash stage.");
      break;
    default:
      return false;
  }

  return true;
}
