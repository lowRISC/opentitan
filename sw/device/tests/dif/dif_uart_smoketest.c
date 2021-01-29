// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static const uint8_t kSendData[] = "Smoke test!";

const test_config_t kTestConfig = {
    .can_clobber_uart = true,
};

bool test_main(void) {
  dif_uart_t uart;
  CHECK(dif_uart_init(
            (dif_uart_params_t){
                .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR),
            },
            &uart) == kDifUartOk);
  CHECK(dif_uart_configure(&uart,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifUartToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifUartConfigOk,
        "UART config failed!");

  CHECK(dif_uart_loopback_set(&uart, kDifUartLoopbackSystem,
                              kDifUartToggleEnabled) == kDifUartOk);
  CHECK(dif_uart_fifo_reset(&uart, kDifUartFifoResetAll) == kDifUartOk);

  // Send all bytes in `kSendData`, and check that they are received via
  // the loopback mechanism.
  for (int i = 0; i < sizeof(kSendData); ++i) {
    CHECK(dif_uart_byte_send_polled(&uart, kSendData[i]) == kDifUartOk);

    uint8_t receive_byte;
    CHECK(dif_uart_byte_receive_polled(&uart, &receive_byte) == kDifUartOk);
    CHECK(receive_byte == kSendData[i]);
  }

  return true;
}
