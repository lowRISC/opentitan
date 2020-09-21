// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper for RISC-V compliance tests, it saves architectural state before
// jumping into the test (via run_rvc_test). After the test completes it dumps
// the signature out via the UART.

#include "sw/device/lib/uart.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/print.h"
#include "sw/device/lib/common.h"

extern void run_rvc_test(void);

extern uint32_t begin_signature[];
extern uint32_t end_signature[];

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);

  run_rvc_test();

  uint32_t size = end_signature - begin_signature;

  for (uint32_t i = 0; i < size; ++i) {
    base_printf("SIG: %08x\r\n", REG32(begin_signature + i));
  }

  return 0;
}
