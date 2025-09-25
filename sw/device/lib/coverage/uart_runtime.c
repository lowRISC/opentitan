// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/coverage/printer.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"

void coverage_transport_init(void) {
  pinmux_init_uart0_tx();
  uart_init(kUartNCOValue);

  // python3 util/uart_hex.py 'COVERAGE:UART\r\n'
  uart_write_imm(0x4547415245564f43);
  uart_write_imm(0x000a0d545241553a);
  while (!uart_tx_idle())
    ;
}

void coverage_report(void) {
  if (coverage_is_valid()) {
    // python3 util/uart_hex.py '== COVERAGE PROFILE START
    // ==\r\n'
    uart_write_imm(0x5245564f43203d3d);
    uart_write_imm(0x464f525020454741);
    uart_write_imm(0x5241545320454c49);
    uart_write_imm(0x00000a0d3d3d2054);

    coverage_printer_run();

    // python3 util/uart_hex.py '== COVERAGE PROFILE END
    // ==\r\n'
    uart_write_imm(0x5245564f43203d3d);
    uart_write_imm(0x464f525020454741);
    uart_write_imm(0x20444e4520454c49);
    uart_write_imm(0x000000000a0d3d3d);
  } else {
    // python3 util/uart_hex.py '== COVERAGE PROFILE DUMPED
    // ==\r\n'
    uart_write_imm(0x5245564f43203d3d);
    uart_write_imm(0x464f525020454741);
    uart_write_imm(0x504d554420454c49);
    uart_write_imm(0x000a0d3d3d204445);
  }

  // Wait until the report is sent.
  while (!uart_tx_idle())
    ;
}

void coverage_printer_sink(const void *data, size_t size) {
  for (size_t i = 0; i < size; ++i) {
    uart_write_hex(((uint8_t *)data)[i], 1, 0);
  }
}
