// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_uart_t uart0;
static const uint8_t kSendData[] = "Sanity test!";

static bool uart_initialise(mmio_region_t base_addr, dif_uart_t *uart) {
  dif_uart_config_t config = {
      .baudrate = kUartBaudrate,
      .clk_freq_hz = kClockFreqHz,
      .parity_enable = kDifUartDisable,
      .parity = kDifUartParityEven,
  };

  return dif_uart_init(base_addr, &config, uart) == kDifUartConfigOk;
}

bool test_main(void) {
  mmio_region_t uart_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR);
  if (!uart_initialise(uart_base_addr, &uart0)) {
    return false;
  }

  // Make sure that the test runner reinitialises UART after this test.
  uart_reconfigure_required = true;

  if (dif_uart_loopback_set(&uart0, kDifUartLoopbackSystem, kDifUartEnable) !=
      kDifUartOk) {
    return false;
  }

  if (dif_uart_fifo_reset(&uart0, kDifUartFifoResetAll) != kDifUartOk) {
    return false;
  }

  // Send all bytes in `kSendData`, and check that they are received via
  // a loopback mechanism.
  for (int i = 0; i < sizeof(kSendData); ++i) {
    if (dif_uart_byte_send_polled(&uart0, kSendData[i]) != kDifUartOk) {
      return false;
    }

    uint8_t receive_byte;
    if (dif_uart_byte_receive_polled(&uart0, &receive_byte) != kDifUartOk) {
      return false;
    }

    if (receive_byte != kSendData[i]) {
      return false;
    }
  }

  return true;
}
