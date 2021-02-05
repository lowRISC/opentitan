// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h" // Generated.

static dif_uart_t uart;

int main(int argc, char **argv) {
  int result;
  result = dif_uart_init((dif_uart_params_t) {
    .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
  }, &uart);
  result = dif_uart_configure(&uart, (dif_uart_config_t) {
    .baudrate = kUartBaudrate,
    .clk_freq_hz = kClockFreqPeripheralHz,
    .parity_enable = kDifUartToggleDisabled,
    .parity = kDifUartParityEven,
  });
  base_uart_stdout(&uart);

  base_printf("Hello, world!\n\r");
  base_printf("Type anything into the console window.\n\r");

  while (true) {
    usleep(10 * 1000);  // 10 ms

    while (true) {
      size_t chars_available;
      if (dif_uart_rx_bytes_available(&uart, &chars_available) != kDifUartOk || chars_available == 0) {
        break;
      }

      uint8_t rcv_char;
      result = dif_uart_bytes_receive(&uart, 1, &rcv_char, NULL);
      result = dif_uart_byte_send_polled(&uart, rcv_char);
    }
  }
  if (result != 0) // This just avoids unused result or variable errors
    base_printf("Something failed.\n\r");
}
