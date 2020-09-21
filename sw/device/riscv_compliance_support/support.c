// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/uart.h"

// These symbopls are provided by the riscv-compliance libraries.
extern void run_rvc_test(void);
extern volatile uint32_t begin_signature[];
extern volatile uint32_t end_signature[];

int opentitan_compliance_main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);

  run_rvc_test();

  ptrdiff_t size = end_signature - begin_signature;
  for (int i = 0; i < size; ++i) {
    base_printf("SIG: %08x\r\n", begin_signature[i]);
  }

  return 0;
}
