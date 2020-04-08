// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>
#include <stdbool.h>

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
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

/**
 * Configuration values for USB.
 */
static uint8_t config_descriptors[] = {
    USB_CFG_DSCR_HEAD(
        USB_CFG_DSCR_LEN + 2 * (USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN),
        2),
    VEND_INTERFACE_DSCR(0, 2, 0x50, 1), USB_BULK_EP_DSCR(0, 1, 32, 0),
    USB_BULK_EP_DSCR(1, 1, 32, 4), VEND_INTERFACE_DSCR(1, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 2, 32, 0), USB_BULK_EP_DSCR(1, 2, 32, 4),
};

/**
 * USB device context types.
 */
static usbdev_ctx_t usbdev;
static usb_controlep_ctx_t usbdev_control;
static usb_ss_ctx_t simple_serial0;
static usb_ss_ctx_t simple_serial1;

/**
 * Makes `c` into a printable character, replacing it with `replacement`
 * as necessary.
 */
static char make_printable(char c, char replacement) {
  if (c == 0xa || c == 0xd) {
    return c;
  }

  if (c < ' ' || c > '~') {
    c = replacement;
  }
  return c;
}

static const size_t kExpectedUsbCharsRecved = 6;
static size_t usb_chars_recved_total;

/**
 * Callbacks for processing USB reciept. The latter increments the
 * recieved character by one, to make them distinct.
 */
static void usb_receipt_callback_0(uint8_t c) {
  c = make_printable(c, '?');
  uart_send_char(c);
  ++usb_chars_recved_total;
}
static void usb_receipt_callback_1(uint8_t c) {
  c = make_printable(c + 1, '?');
  uart_send_char(c);
  ++usb_chars_recved_total;
}

static dif_gpio_t gpio;

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  pinmux_init();
  spid_init();

  dif_gpio_config_t gpio_config = {.base_addr =
                                       mmio_region_from_addr(0x40010000)};
  dif_gpio_init(&gpio_config, &gpio);
  // Enable GPIO: 0-7 and 16 is input; 8-15 is output.
  dif_gpio_output_mode_all_set(&gpio, 0x0ff00);

  LOG_INFO("Hello, USB!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  demo_gpio_startup(&gpio);

  // Call `usbdev_init` here so that DPI will not start until the
  // simulation has finished all of the printing, which takes a while
  // if `--trace` was passed in.
  usbdev_init(&usbdev);
  usb_controlep_init(&usbdev_control, &usbdev, 0, config_descriptors,
                     sizeof(config_descriptors));
  usb_simpleserial_init(&simple_serial0, &usbdev, 1, usb_receipt_callback_0);
  usb_simpleserial_init(&simple_serial1, &usbdev, 2, usb_receipt_callback_1);

  spid_send("SPI!", 4);

  uint32_t gpio_state = 0;
  bool pass_signaled = false;
  while (true) {
    usbdev_poll(&usbdev);

    gpio_state = demo_gpio_to_log_echo(&gpio, gpio_state);
    demo_spi_to_log_echo();

    char rcv_char;
    while (uart_rcv_char(&rcv_char) != -1) {
      uart_send_char(rcv_char);
      dif_gpio_all_write(&gpio, rcv_char << 8);

      if (rcv_char == '/') {
        uint32_t usb_irq_state = REG32(USBDEV_INTR_STATE());
        uint32_t usb_stat = REG32(USBDEV_USBSTAT());
        LOG_INFO("I%4x-%8x", usb_irq_state, usb_stat);
      } else {
        usb_simpleserial_send_byte(&simple_serial0, rcv_char);
        usb_simpleserial_send_byte(&simple_serial1, rcv_char + 1);
      }
    }

    // Signal that the simulation succeeded.
    if (usb_chars_recved_total >= kExpectedUsbCharsRecved && !pass_signaled) {
      uart_send_str("\r\n");
      uart_send_str("PASS!\r\n");
      pass_signaled = true;
    }
  }

  uart_send_str("\r\n");
  LOG_INFO("USB recieved %d characters.", usb_chars_recved_total);
}
