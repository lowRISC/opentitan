// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint8_t kSendData[] = "Smoke test!";

const test_config_t kTestConfig = {
    .enable_concurrency = false,
    .can_clobber_uart = true,
};

bool test_main(void) {
  dif_uart_t uart;
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));
  CHECK(dif_uart_configure(&uart,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifOk,
        "UART config failed!");

  CHECK_DIF_OK(
      dif_uart_loopback_set(&uart, kDifUartLoopbackSystem, kDifToggleEnabled));
  CHECK_DIF_OK(dif_uart_fifo_reset(&uart, kDifUartFifoResetAll));

  // Send all bytes in `kSendData`, and check that they are received via
  // the loopback mechanism.
  for (int i = 0; i < sizeof(kSendData); ++i) {
    CHECK_DIF_OK(dif_uart_byte_send_polled(&uart, kSendData[i]));

    uint8_t receive_byte;
    CHECK_DIF_OK(dif_uart_byte_receive_polled(&uart, &receive_byte));
    CHECK(receive_byte == kSendData[i]);
  }

  return true;
}
