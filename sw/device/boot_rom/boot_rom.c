// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/boot_rom/bootstrap.h"
#include "sw/device/boot_rom/chip_info.h"  // Generated.
#include "sw/device/lib/common.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/gpio.h"
#include "sw/device/lib/log.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"

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
  pinmux_init();
  uart_init(UART_BAUD_RATE);
  uart_send_str((char *)chip_info);

  int rv = bootstrap();
  if (rv) {
    LOG_ERROR("Bootstrap failed with status code: %d\n", rv);
    // Currently the only way to recover is by a hard reset.
    return rv;
  }

  LOG_INFO("Jump!\n");
  while (!uart_tx_empty()) {
  }
  try_launch();
}
