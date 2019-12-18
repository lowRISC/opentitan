// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/gpio.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"

#define SPI_MAX 32

// called from ctr0 when something bad happens
// char I=illegal instruction, A=lsu error (address), E=ecall
void trap_handler(uint32_t mepc, char c) {
  uart_send_char(c);
  uart_send_uint(mepc, 32);
  while (1) {
    gpio_write_all(0xAA00);  // pattern
    busy_sleep_micros(200 * 1000);
    gpio_write_all(0x5500);  // pattern
    busy_sleep_micros(100 * 1000);
  }
}

#define MK_PRINT(c) (((c < 32) || (c > 126)) ? '_' : c)

int main(int argc, char **argv) {
  uart_init(UART_BAUD_RATE);

  pinmux_init();
  // Enable GPIO: 0-7 and 16 is input, 8-15 is output
  gpio_init(0xFF00);

  spid_init();
  // Add DATE and TIME because I keep fooling myself with old versions
  uart_send_str(
      "Hello World! "__DATE__
      " "__TIME__
      "\r\n");
  uart_send_str("Watch the LEDs!\r\n");

  // Give a LED pattern as startup indicator for 5 seconds
  gpio_write_all(0xFF00);  // all LEDs on
  for (int i = 0; i < 32; i++) {
    busy_sleep_micros(100 * 1000);  // 100 ms

    gpio_write_bit(8 + (i % 8), (i / 8));
  }

  // Now have UART <-> Buttons/LEDs demo
  // all LEDs off
  gpio_write_all(0x0000);
  uart_send_str("Try out the switches on the board\r\n");
  uart_send_str("or type anything into the console window.\r\n");
  uart_send_str("The LEDs show the ASCII code of the last character.\r\n");

  uint32_t gpio_in;
  uint32_t gpio_in_prev = 0;
  uint32_t gpio_in_changes;
  uint8_t spi_buf[SPI_MAX];
  uint32_t spi_in;

  spid_send("SPI!", 4);

  while (1) {
    busy_sleep_micros(10 * 1000);  // 10 ms

    // report changed switches over UART
    gpio_in = gpio_read() & 0x100FF;  // 0-7 is switch input, 16 is FTDI
    gpio_in_changes = (gpio_in & ~gpio_in_prev) | (~gpio_in & gpio_in_prev);
    for (int b = 0; b < 8; b++) {
      if (gpio_in_changes & (1 << b)) {
        int val_now = (gpio_in >> b) & 0x01;
        uart_send_str("GPIO: Switch ");
        uart_send_char(b + 48);
        uart_send_str(" changed to ");
        uart_send_char(val_now + 48);
        uart_send_str("\r\n");
      }
    }
    if (gpio_in_changes & 0x10000) {
      uart_send_str("FTDI control changed. Enable ");
      uart_send_str((gpio_in & 0x10000) ? "JTAG\r\n" : "SPI\r\n");
    }
    gpio_in_prev = gpio_in;

    // SPI character echo
    spi_in = spid_read_nb(spi_buf, SPI_MAX);
    if (spi_in) {
      uint32_t d = (*(uint32_t *)spi_buf) ^ 0x01010101;
      spid_send(&d, 4);
      uart_send_str("SPI: ");
      for (int i = 0; i < spi_in; i++) {
        uart_send_char(MK_PRINT(spi_buf[i]));
      }
      uart_send_str("\r\n");
    }
    // UART echo
    char rcv_char;
    while (uart_rcv_char(&rcv_char) != -1) {
      uart_send_char(rcv_char);
      gpio_write_all(rcv_char << 8);
    }
  }
}
