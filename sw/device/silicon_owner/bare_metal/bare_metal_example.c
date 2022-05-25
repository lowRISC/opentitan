// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

void bare_metal_init(void) {
  pinmux_init();
  uart_init(kUartNCOValue);
  base_set_stdout((buffer_sink_t){
      .data = NULL,
      .sink = uart_sink,
  });
}

void bare_metal_main(void) {
  bare_metal_init();

  // The PASS string is scanned by system test scripts. See
  // test/systemtest/earlgrey/test_fpga_cw310.py for more details.
  base_printf("Bare metal PASS!\r\n");

  while (true) {
  }
}

void interrupt_handler(void) {}

// We only need a single handler for all interrupts, but we want to
// keep distinct symbols to make writing tests easier.
void exception_handler(void) __attribute__((alias("interrupt_handler")));

void nmi_handler(void) __attribute__((alias("interrupt_handler")));
