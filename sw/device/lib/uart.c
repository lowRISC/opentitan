// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/uart.h"

#include "sw/device/lib/common.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#define UART0_BASE_ADDR 0x40000000

static dif_uart_t uart0;

void uart_init(unsigned int baud) {
  dif_uart_config_t config = {
      .baudrate = baud,
      .clk_freq_hz = kIbexClockFreqHz,
      .parity_enable = kDifUartDisable,
      .parity = kDifUartParityEven,
  };

  mmio_region_t base_addr = mmio_region_from_addr(UART0_BASE_ADDR);
  (void)dif_uart_init(base_addr, &config, &uart0);
}

void uart_send_char(char c) {
  (void)dif_uart_byte_send_polled(&uart0, (uint8_t)c);
}

void uart_send_str(char *str) {
  while (*str != '\0') {
    uart_send_char(*str++);
  }
}

#define hexchar(i) (((i & 0xf) > 9) ? (i & 0xf) - 10 + 'A' : (i & 0xf) + '0')

void uart_send_uint(uint32_t n, int bits) {
  for (int i = bits - 4; i >= 0; i -= 4) {
    uart_send_char(hexchar(n >> i));
  }
}

int uart_rcv_char(char *c) {
  size_t num_bytes = 0;
  if (!dif_uart_rx_bytes_available(&uart0, &num_bytes)) {
    return -1;
  }
  if (num_bytes == 0) {
    return -1;
  }
  // The pointer cast from char* to uint8_t* is dangerous. This needs to be
  // revisited.
  return dif_uart_bytes_receive(&uart0, 1, (uint8_t *)c, NULL) ? 0 : -1;
}
