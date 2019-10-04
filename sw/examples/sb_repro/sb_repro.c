// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "common.h"
#include "gpio.h"
#include "spi_device.h"
#include "uart.h"

#define SPI_MAX 32

/**
 * Delay loop executing within 8 cycles on ibex
 */
static void delay_loop_ibex(unsigned long loops) {
  int out; /* only to notify compiler of modifications to |loops| */
  asm volatile(
      "1: nop             \n"  // 1 cycle
      "   nop             \n"  // 1 cycle
      "   nop             \n"  // 1 cycle
      "   nop             \n"  // 1 cycle
      "   addi %1, %1, -1 \n"  // 1 cycle
      "   bnez %1, 1b     \n"  // 3 cycles
      : "=&r"(out)
      : "0"(loops));
}

static int usleep_ibex(unsigned long usec) {
  unsigned long usec_cycles;
  usec_cycles = CLK_FIXED_FREQ_HZ * usec / 1000 / 1000 / 8;

  delay_loop_ibex(usec_cycles);
  return 0;
}

static int usleep(unsigned long usec) { return usleep_ibex(usec); }

// called from ctr0 when something bad happens
// char I=illegal instruction, A=lsu error (address), E=ecall
void trap_handler(uint32_t mepc, char c) {
  uart_send_char(c);
  uart_send_uint(mepc, 32);
  while (1) {
    gpio_write_all(0xAA00);  // pattern
    usleep(200 * 1000);
    gpio_write_all(0x5500);  // pattern
    usleep(100 * 1000);
  }
}

#define MK_PRINT(c) (((c < 32) || (c > 126)) ? '_' : c)

void print_hex(char *label, size_t val, size_t bits) {
  uart_send_str(label);
  uart_send_str(" = 0x");
  uart_send_uint(val, bits);
  uart_send_str(";\r\n");
}

#define HEX(val) print_hex(#val, val, 8 * sizeof(val))

int main(int argc, char **argv) {
  uart_init(UART_BAUD_RATE);

  // Enable GPIO: 0-7 and 16 is input, 8-15 is output
  gpio_init(0xFF00);

  spid_init();
  // Add DATE and TIME because I keep fooling myself with old versions
  uart_send_str(
      "Hello World! "__DATE__
      " "__TIME__
      "\r\n");

  // Create a character array, to force allocation in RAM with
  // |alignof == 1|. Initialize it to avoid UB from reading it.
  char buf[8] = {0, 1, 2, 3, 4, 5, 6, 7};

  // Assert that its address 4-byte aligned.
  HEX((size_t) buf);

  // Read the first character (aligned load) and the second
  // (unaligned load). These should both compile to |lb| or |lbu|
  // instructions.
  HEX(buf[0]);
  HEX(buf[1]);

  // Write to the first character (aligned store) and the second
  // (unaligned store). These should both compile to |sb|, but the
  // second should fault (a bug!).
  HEX(buf[0] = 0xa);
  HEX(buf[1] = 0xb);

  // Print part of the buffer to trick the compiler into not deleting
  // the above loads and stores.
  uart_send_uint(*(uint32_t *) buf, 32);

  for (;;) {}
}
