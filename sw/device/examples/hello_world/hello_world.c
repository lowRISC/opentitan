// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/print.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"

#define SPI_MAX 32
#define GPIO0_BASE_ADDR 0x40010000u

static dif_gpio_t gpio;

// called from ctr0 when something bad happens
// char I=illegal instruction, A=lsu error (address), E=ecall
void trap_handler(uint32_t mepc, char c) {
  uart_send_char(c);
  uart_send_uint(mepc, 32);
  while (1) {
    dif_gpio_all_write(&gpio, 0xAA00);  // pattern
    usleep(200 * 1000);
    dif_gpio_all_write(&gpio, 0x5500);  // pattern
    usleep(100 * 1000);
  }
}

#define MK_PRINT(c) (((c < 32) || (c > 126)) ? '_' : c)

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);
  
  pinmux_init();
  spid_init();
  // Enable GPIO: 0-7 and 16 is input, 8-15 is output
  dif_gpio_config_t gpio_config = {.base_addr =
                                       mmio_region_from_addr(GPIO0_BASE_ADDR)};
  dif_gpio_init(&gpio_config, &gpio);
  dif_gpio_output_mode_all_set(&gpio, 0xFF00);
  // Add DATE and TIME because I keep fooling myself with old versions
  base_printf("Hello World!\r\n");
  base_printf("Built at: " __DATE__ ", " __TIME__ "\r\n");
  base_printf("Watch the LEDs!\r\n");

  // Give a LED pattern as startup indicator for 5 seconds
  dif_gpio_all_write(&gpio, 0xFF00);  // all LEDs on
  for (int i = 0; i < 32; i++) {
    usleep(100 * 1000);  // 100 ms

    dif_gpio_pin_write(&gpio, 8 + (i % 8), (i / 8) % 2);
  }

  // Now have UART <-> Buttons/LEDs demo
  // all LEDs off
  dif_gpio_all_write(&gpio, 0x0000);
  base_printf("Try out the switches on the board\r\n");
  base_printf("or type anything into the console window.\r\n");
  base_printf("The LEDs show the ASCII code of the last character.\r\n");

  uint32_t gpio_in;
  uint32_t gpio_in_prev = 0;
  uint32_t gpio_in_changes;
  uint8_t spi_buf[SPI_MAX];
  uint32_t spi_in;

  spid_send("SPI!", 4);

  while (1) {
    usleep(10 * 1000);  // 10 ms

    // report changed switches over UART
    dif_gpio_all_read(&gpio, &gpio_in);
    gpio_in &= 0x100FF;  // 0-7 is switch input, 16 is FTDI
    gpio_in_changes = (gpio_in & ~gpio_in_prev) | (~gpio_in & gpio_in_prev);
    for (int b = 0; b < 8; b++) {
      if (gpio_in_changes & (1 << b)) {
        int val_now = (gpio_in >> b) & 0x01;
        base_printf("GPIO: Switch %d changed to %d\r\n", b, val_now);
      }
    }
    if (gpio_in_changes & 0x10000) {
      const char *port_type = (gpio_in & 0x10000) ? "JTAG" : "SPI";
      base_printf("FTDI control changed. Enable %s.\r\n", port_type);
    }
    gpio_in_prev = gpio_in;

    // SPI character echo
    spi_in = spid_read_nb(spi_buf, SPI_MAX);
    if (spi_in) {
      uint32_t d = (*(uint32_t *)spi_buf) ^ 0x01010101;
      spid_send(&d, 4);
      base_printf("SPI: ");
      for (int i = 0; i < spi_in; i++) {
        base_printf("%c", MK_PRINT(spi_buf[i]));
      }
      base_printf("\r\n");
    }
    // UART echo
    char rcv_char;
    while (uart_rcv_char(&rcv_char) != -1) {
      uart_send_char(rcv_char);
      dif_gpio_all_write(&gpio, rcv_char << 8);
    }
  }
}
