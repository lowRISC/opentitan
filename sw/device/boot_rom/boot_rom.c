// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

/**
 * This symbol is defined in sw/device/boot_rom/rom_link.ld,
 * and describes the location of the flash header.
 *
 * The actual contents are not defined by the ROM, but rather
 * by the flash binary: see sw/device/exts/common/flash_link.ld
 * for that.
 */
extern struct {
  void (*entry)(void);
} _flash_header;

void _boot_start(void) {
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

  // Jump into flash. At this point, the contents of the flash binary have been
  // verified, and we can transfer control directly to it. It is the
  // flash binary's responsibily to set up its own stack, and to never
  // return.
  _flash_header.entry();
}
