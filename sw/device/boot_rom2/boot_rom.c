// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0`

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/boot_rom2/final_jump.h"
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

  extern noreturn void _reset_start(next_stage_args_t *);

  // Temporary placeholder, to show that final jump actually works.
  // All this does is pass the end of ram as the stack bottom, and uses the boot
  // ROM's own reset handler as the entry point.
  //
  // This simply causes the boot ROM to recurse forever.
  void *stack_bottom = (void *)(0x10000000 + 0x10000);
  final_jump(&_reset_start, (next_stage_args_t){
                                .stack_start = stack_bottom,
                            });
}
