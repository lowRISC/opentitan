// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_uart_t uart0;
static dif_pinmux_t pinmux;
static dif_otp_ctrl_t otp;

static const uint8_t kNumDeviceId = 8;

static const char kTestDeviceID[] = "abcdefghijklmno";
static_assert(ARRAYSIZE(kTestDeviceID) % sizeof(uint32_t) == 0,
              "kTestDeviceID must be a word array");
static_assert(ARRAYSIZE(kTestDeviceID) <= 32,
              "kTestDeviceID must be less than 32 bytes");

static status_t log_device_id() {
  // Read the Device_ID from OTP (except all zeroes).
  uint32_t otp_device_id;
  for (int i = 0; i < kNumDeviceId; i++) {
    TRY(otp_ctrl_testutils_dai_read32(&otp, kDifOtpCtrlPartitionHwCfg, i * 4,
                                      &otp_device_id));

    LOG_INFO("Device_ID_%d = %08x", i, otp_device_id);
  }
  return OK_STATUS();
}

status_t write_otp() {
  // Configure the pinmux.
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  pinmux_testutils_init(&pinmux);

  // Initialize UART.
  TRY(dif_uart_init(mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
                    &uart0));
  TRY(dif_uart_configure(&uart0, (dif_uart_config_t){
                                     .baudrate = kUartBaudrate,
                                     .clk_freq_hz = kClockFreqPeripheralHz,
                                     .parity_enable = kDifToggleDisabled,
                                     .parity = kDifUartParityEven,
                                     .tx_enable = kDifToggleEnabled,
                                     .rx_enable = kDifToggleEnabled,
                                 }));
  base_uart_stdout(&uart0);

  LOG_INFO("Initializing OTP...");
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  TRY(dif_otp_ctrl_configure(&otp, config));

  // Read the Device_ID from OTP (except all zeroes).
  log_device_id();
  // Program the Device_ID.
  for (int i = 0; i < ARRAYSIZE(kTestDeviceID); i += sizeof(uint32_t)) {
    uint32_t word;
    memcpy(&word, &kTestDeviceID[i], sizeof(word));

    TRY(otp_ctrl_testutils_wait_for_dai(&otp));
    TRY(dif_otp_ctrl_dai_program32(&otp, kDifOtpCtrlPartitionHwCfg, i * 4,
                                   word));
  }
  // Read the Device_ID from OTP (except correct data).
  log_device_id();

  return OK_STATUS();
}

void sram_main() {
  status_t res = write_otp();
  LOG_INFO("result: %x", res);
  test_status_set(kTestStatusPassed);
}
