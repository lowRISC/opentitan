// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdnoreturn.h>

#include "sw/device/boot_rom/bootstrap.h"
#include "sw/device/boot_rom/chip_info.h"  // Generated.
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/gpio.h"
#include "sw/device/lib/log.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"

static noreturn void try_launch(void) {
  asm volatile(
      "  la   sp, _stack_start;"
      "  tail _flash_start;"
      // Unfortunately, we can't tell the compiler that we're about to clobber
      // the stack pointer (which is meaningless, since there's nowhere to spill
      // sp to). However, this doesn't matter, since this asm block will never
      // return.
      :
      :
      : /* sp, */ "memory");
  __builtin_unreachable();
}

void _boot_start() {
  pinmux_init();
  uart_init(UART_BAUD_RATE);
  uart_send_str((char *)chip_info);

  int bootstrap_err = bootstrap();
  if (bootstrap_err != 0) {
    LOG_ERROR("Bootstrap failed with status code: %d\n", bootstrap_err);
    // Currently the only way to recover is by a hard reset.
    return;
  }

  LOG_INFO("Boot ROM initialisation has completed, jump into flash!\n");
  while (!uart_tx_empty()) {
  }

  try_launch();
}
