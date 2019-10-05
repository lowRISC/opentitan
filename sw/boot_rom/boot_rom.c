// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "bootstrap.h"
#include "chip_info.h"
#include "common.h"
#include "flash_ctrl.h"
#include "gpio.h"
#include "msg.h"
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
  uart_send_str((char *)chip_info);

  int rv = bootstrap();
  if (rv) {
    MSG_ERROR("Bootstrap failed with status code: %d\n", rv);
    // Currently the only way to recover is by a hard reset.
    return rv;
  }

  MSG_INFO("Jump!\n");
  while (!uart_tx_empty()) {
  }
  try_launch();
}
