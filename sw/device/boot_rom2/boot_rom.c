// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0`

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/boot_rom2/uart_log.h"
#include "sw/device/lib/base/log.h"

// Non-DIF drivers. These should eventually be removed.
#include "sw/device/lib/pinmux.h"

/**
 * First non-assembly function, called by the ROM CRT file.
 *
 * Returning from this function is equivalent to aborting.
 */
void _boot_start(void) {
  pinmux_init();
  uart_log_init();

  LOG_INFO("Hello, world!");
}
