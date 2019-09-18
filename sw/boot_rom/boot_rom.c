// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "bootstrap.h"
#include "common.h"
#include "flash_ctrl.h"
#include "gpio.h"
#include "spi_device.h"
#include "uart.h"

static inline void try_launch(void) {
  __asm__ volatile(
      "la a0, _flash_start;"
      "la sp, _stack_start;"
      "jr a0;"
      :
      :
      :);
}

int main(int argc, char **argv) {
  uart_init(UART_BAUD_RATE);

  int rv = bootstrap();
  if (rv) {
    uart_send_str("Bootstrap failed with status code: ");
    uart_send_uint(rv, 32);
    uart_send_str("\r\n");
    // Currently the only way to recover is by a hard reset.
    return rv;
  }

  uart_send_str("Jump!\r\n");
  while (!uart_tx_empty()) {
  }
  try_launch();
}
