// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/stack_utilization.h"

#include "sw/device/silicon_creator/lib/drivers/uart.h"

#ifdef STACK_UTILIZATION_CHECK
void stack_utilization_print(void) {
  extern uint32_t _stack_start[], _stack_end[];
  // We configure a No-Access ePMP NA4 region at stack_start as a
  // stack guard.  We cannot access that word, so start the scan
  // after the stack guard.
  const uint32_t *sp = _stack_start + 1;
  uint32_t free = 0;
  uint32_t total = (uintptr_t)_stack_end - (uintptr_t)_stack_start;
  while (sp < _stack_end && *sp == STACK_UTILIZATION_FREE_PATTERN) {
    free += sizeof(uint32_t);
    sp++;
  }
  uint32_t used = total - free;
  //                          : K T S
  const uint32_t kPrefix = 0x3a4b5453;
  uart_write_imm(kPrefix);
  uart_write_hex(used, sizeof(used), '/');
  uart_write_hex(total, sizeof(total), '\r');
  // Send the last char with putchar so we'll wait for the
  // transmitter to finish.
  uart_putchar('\n');
}
#endif
