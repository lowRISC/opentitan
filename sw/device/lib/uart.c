// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/uart.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_uart_t uart0;

void uart_init(unsigned int baud) {
  // Note that, due to a GCC bug, we cannot use the standard `(void) expr`
  // syntax to drop this value on the ground.
  // See https://gcc.gnu.org/bugzilla/show_bug.cgi?id=25509
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR);
  if (dif_uart_init((dif_uart_params_t){.base_addr = base_addr}, &uart0)) {
  }
  if (dif_uart_configure(&uart0, (dif_uart_config_t){
                                     .baudrate = baud,
                                     .clk_freq_hz = kClockFreqPeripheralHz,
                                     .parity_enable = kDifUartToggleDisabled,
                                     .parity = kDifUartParityEven,
                                 })) {
  }
}

void uart_send_char(char c) {
  // Note that, due to a GCC bug, we cannot use the standard `(void) expr`
  // syntax to drop this value on the ground.
  // See https://gcc.gnu.org/bugzilla/show_bug.cgi?id=25509
  if (dif_uart_byte_send_polled(&uart0, (uint8_t)c)) {
  }
}

void uart_send_str(char *str) {
  while (*str != '\0') {
    uart_send_char(*str++);
  }
}

size_t uart_send_buf(void *data, const char *buf, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    uart_send_char(buf[i]);
  }
  return len;
}

const buffer_sink_t uart_stdout = {
    .data = NULL, .sink = &uart_send_buf,
};

#define hexchar(i) (((i & 0xf) > 9) ? (i & 0xf) - 10 + 'A' : (i & 0xf) + '0')

void uart_send_uint(uint32_t n, int bits) {
  for (int i = bits - 4; i >= 0; i -= 4) {
    uart_send_char(hexchar(n >> i));
  }
}

int uart_rcv_char(char *c) {
  size_t num_bytes = 0;
  if (dif_uart_rx_bytes_available(&uart0, &num_bytes) != kDifUartOk) {
    return -1;
  }
  if (num_bytes == 0) {
    return -1;
  }
  // The pointer cast from char* to uint8_t* is dangerous. This needs to be
  // revisited.
  if (dif_uart_bytes_receive(&uart0, 1, (uint8_t *)c, NULL) != kDifUartOk) {
    return -1;
  }

  return 0;
}
