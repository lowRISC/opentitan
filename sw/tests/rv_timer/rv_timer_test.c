// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "rv_timer.h"

#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "irq.h"
#include "uart.h"

static uint32_t intr_handling_success = 0;
static const uint32_t hart = 0;

int main(int argc, char **argv) {
  uint64_t cmp = 0x00000000000000FF;

  uart_init(UART_BAUD_RATE);

  irq_global_ctrl(true);
  irq_timer_ctrl(true);
  rv_timer_set_us_tick(hart);
  rv_timer_set_cmp(hart, cmp);
  rv_timer_ctrl(hart, true);
  rv_timer_intr_enable(hart, true);

  while (1) {
    if (intr_handling_success) {
      break;
    }
  }

  uart_send_str("PASS!\r\n");
  __asm__ volatile("wfi;");
}

// Override weak default function
void handler_irq_timer(void) {
  rv_timer_ctrl(hart, false);
  rv_timer_clr_all_intrs();
  intr_handling_success = 1;
}
