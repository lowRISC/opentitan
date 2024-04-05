// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void bare_metal_main(void) {
  dbg_printf("Bare metal PASS!\r\n");
  while (true) {
  }
}

void interrupt_handler(void) { dbg_printf("Interrupt!\r\n"); }

// We only need a single handler for all interrupts, but we want to
// keep distinct symbols to make writing tests easier.
void exception_handler(void) __attribute__((alias("interrupt_handler")));

void nmi_handler(void) __attribute__((alias("interrupt_handler")));
