// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"
#include "sw/device/lib/usb_controlep.h"
#include "sw/device/lib/usb_simpleserial.h"
#include "sw/device/lib/usbdev.h"

// These just for the '/' printout
#define USBDEV_BASE_ADDR 0x40150000
#include "usbdev_regs.h"  // Generated.

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

#define MK_PRINT(c) \
  (((c != 0xa) && (c != 0xd) && ((c < 32) || (c > 126))) ? '_' : c)

// Build Configuration descriptor array
static uint8_t cfg_dscr[] = {
    USB_CFG_DSCR_HEAD(
        USB_CFG_DSCR_LEN + 2 * (USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN),
        2) VEND_INTERFACE_DSCR(0, 2, 0x50, 1) USB_BULK_EP_DSCR(0, 1, 32, 0)
        USB_BULK_EP_DSCR(1, 1, 32, 4) VEND_INTERFACE_DSCR(1, 2, 0x50, 1)
            USB_BULK_EP_DSCR(0, 2, 32, 0) USB_BULK_EP_DSCR(1, 2, 32, 4)};
// The array above may not end aligned on a 4-byte boundary
// and is probably at the end of the initialized data section
// Conversion to srec needs this to be aligned so force it by
// initializing an int32 (volatile else it is not used and can go away)
static volatile int32_t sdata_align = 42;

/* context areas */
static usbdev_ctx_t usbdev_ctx;
static usb_controlep_ctx_t control_ctx;
static usb_ss_ctx_t ss_ctx[2];

// We signal PASS! after receiving USB_MAX.
static volatile unsigned int num_chars_rx = 0;
#ifndef USB_MAX
#define USB_MAX 6
#endif

/* Inbound USB characters get printed to the UART via these callbacks */
/* Not ideal because the UART is slower */
static void serial_rx0(uint8_t c) {
  uart_send_char(MK_PRINT(c));
  num_chars_rx++;
}
/* Add one to rx character so you can tell it is the second instance */
static void serial_rx1(uint8_t c) {
  uart_send_char(MK_PRINT(c + 1));
  num_chars_rx++;
}

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  pinmux_init();
  spid_init();
  // Enable GPIO: 0-7 and 16 is input, 8-15 is output
  dif_gpio_config_t gpio_config = {.base_addr =
                                       mmio_region_from_addr(GPIO0_BASE_ADDR)};
  dif_gpio_init(&gpio_config, &gpio);
  dif_gpio_output_mode_all_set(&gpio, 0xFF00);

  // Add DATE and TIME because I keep fooling myself with old versions
  uart_send_str(
      "Hello USB! "__DATE__
      " "__TIME__
      "\r\n");
  uart_send_str("Characters from UART go to USB and GPIO\r\n");
  uart_send_str("Characters from USB go to UART\r\n");

  // Give a LED pattern as startup indicator for 5 seconds
  dif_gpio_all_write(&gpio, 0xAA00);  // pattern
  usleep(1000);
  dif_gpio_all_write(&gpio, 0x5500);  // pattern
  // usbdev_init here so dpi code will not start until simulation
  // got through all the printing (which takes a while if --trace)
  usbdev_init(&usbdev_ctx);
  usb_controlep_init(&control_ctx, &usbdev_ctx, 0, cfg_dscr, sizeof(cfg_dscr));
  usb_simpleserial_init(&ss_ctx[0], &usbdev_ctx, 1, serial_rx0);
  usb_simpleserial_init(&ss_ctx[1], &usbdev_ctx, 2, serial_rx1);
  bool pass_signaled = false;

  uint32_t gpio_in;
  uint32_t gpio_in_prev = 0;
  uint32_t gpio_in_changes;
  uint8_t spi_buf[SPI_MAX];
  uint32_t spi_in;

  spid_send("SPI!", 4);

  while (1) {
    usbdev_poll(&usbdev_ctx);

    // report changed switches over UART
    dif_gpio_all_read(&gpio, &gpio_in);
    gpio_in &= 0x100FF;  // 0-7 is switch input, 16 is FTDI
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
      dif_gpio_all_write(&gpio, rcv_char << 8);
      if (rcv_char == '/') {
        uart_send_char('I');
        uart_send_uint(REG32(USBDEV_INTR_STATE()), 16);
        uart_send_char('-');
        uart_send_uint(REG32(USBDEV_USBSTAT()), 32);
        uart_send_char(' ');
      } else {
        usb_simpleserial_send_byte(&ss_ctx[0], rcv_char);
        usb_simpleserial_send_byte(&ss_ctx[1], rcv_char + 1);
      }
    }

    // Signal that the simulation passed
    if ((num_chars_rx >= USB_MAX) && (pass_signaled == false)) {
      uart_send_str("\r\nPASS!\r\n");
      pass_signaled = true;
    }
  }
  uart_send_str("\r\nUSB received 0x");
  uart_send_uint(num_chars_rx, 32);
  uart_send_str(" characters.\r\n");
}
