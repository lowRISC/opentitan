// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"

void coverage_transport_init(void) {
  pinmux_init_uart0_tx();
  uart_init(kUartNCOValue);

  dbg_puts("COV_SKIP:UART\r\n");
  while (!uart_tx_idle()) {
  }
}

void coverage_init(void) {}

void coverage_report(void) {
  dbg_puts("\x10== COVERAGE PROFILE SKIP ==\r\n");

  // Wait until the report is sent.
  while (!uart_tx_idle()) {
  }
}

void coverage_invalidate(void) {}
