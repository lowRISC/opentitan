// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"

void coverage_transport_init(void) {
  pinmux_init_uart0_tx();
  uart_init(kUartNCOValue);

  // python3 util/uart_hex.py 'COV_SKIP:UART\r\n'
  uart_write_imm(0x50494b535f564f43);
  uart_write_imm(0x000a0d545241553a);
  while (!uart_tx_idle())
    ;
}

void coverage_init(void) {}

void coverage_report(void) {
  // python3 util/uart_hex.py '== COVERAGE PROFILE SKIP
  // ==\r\n'
  uart_write_imm(0x5245564f43203d3d);
  uart_write_imm(0x464f525020454741);
  uart_write_imm(0x50494b5320454c49);
  uart_write_imm(0x0000000a0d3d3d20);

  // Wait until the report is sent.
  while (!uart_tx_idle())
    ;
}

void coverage_invalidate(void) {}
