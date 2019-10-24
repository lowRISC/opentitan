// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "bootstrap.h"
#include "chip_info.h"
#include "common.h"
#include "flash_ctrl.h"
#include "gpio.h"
#include "spi_device.h"
#include "uart.h"

static NO_RETURN void try_launch(void) {
  __asm__ volatile("  la sp, _stack_start\n"
                   "  tail _flash_start"
                   // Make sure to tell the compiler we plan to clobber
                   // *everything*.
                   ::: "memory", "sp");
  // This loop doesn't really do anything, since the jump in the above assembly
  // doesn't set up a link register. It mostly exists to stop the compiler from
  // detecting UB from this function managing to return.
  for (;;) {
    __asm__ volatile("wfi");
  }
}

void _boot_rom(void) {
  uart_init(UART_BAUD_RATE);
  uart_send_str((char *)chip_info);

  int rv = bootstrap();
  if (rv != 0) {
    uart_send_str("Bootstrap failed with status code: ");
    uart_send_uint(rv, 32);
    uart_send_str("\r\n");
    // Currently the only way to recover is by a hard reset.
    return rv;
  }

  uart_send_str("Jump!\r\n");
  while (!uart_tx_empty()) {}
  try_launch();
}
