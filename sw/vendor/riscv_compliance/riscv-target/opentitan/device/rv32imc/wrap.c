// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "common.h"
#include "uart.h"

#define SIM_TERM_ADDR 0x10008000

void dump_signature(void) {
  extern uint32_t begin_signature[];
  extern uint32_t end_signature[];

  uint32_t size = end_signature - begin_signature;
  uart_init(UART_BAUD_RATE);
  // uart_send_str("PASS!\r\n");
  for (uint32_t i = 0; i < size; i++) {
    uart_send_str("SIG: ");
    uart_send_uint(REG32(begin_signature + i), 32);
    uart_send_str("\r\n");
  }

  uart_send_str("PASS!\r\n");
  uart_send_str("End");
  // wait for all uart outputs to complete
  while (!uart_tx_empty() || !uart_tx_idle()) {
  };

  // terminate simulation
  REG32(SIM_TERM_ADDR) = 0;
  __asm__ volatile("wfi;");
}
