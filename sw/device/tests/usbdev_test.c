// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB device test
//
// This test is a stripped down version of the hello_usbdev example application.
// It requires interaction with the USB DPI model mimicking the host and thus
// can only be run in the Verilator simulation. The test initializes the USB
// device and configures USB Endpoint 1 as a simpleserial endpoint. The test
// then starts polling the USB device for data sent by the host. Any data
// received on Endpoint 1 is stored in a buffer and printed via UART.
//
// The DPI model mimicks the USB host. After device initialization, it detects
// the assertion of the pullup and first assigns an address to the device. It
// then sends various USB transactions to the device including two OUT
// transactions with a data payload of "Hi!" to Endpoint 1. If these two OUT
// transactions are succesfully received by the device, the test passes.

#include "sw/device/lib/usbdev.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/usb_controlep.h"
#include "sw/device/lib/usb_simpleserial.h"

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
static usb_ss_ctx_t simple_serial;

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
static const char kExpectedUsbRecved[7] = "Hi!Hi!";
static size_t usb_chars_recved_total;
static char buffer[7];

/**
 * Callback for processing USB reciept.
 */
static void usb_receipt_callback(uint8_t c) {
  c = make_printable(c, '?');
  base_printf("%c", c);
  if (usb_chars_recved_total < kExpectedUsbCharsRecved) {
    buffer[usb_chars_recved_total] = c;
    ++usb_chars_recved_total;
  }
}

const test_config_t kTestConfig;

bool test_main(void) {
  CHECK(kDeviceType == kDeviceSimVerilator,
        "This test is not expected to run on platforms other than the "
        "Verilator simulation. It needs the USB DPI model.");

  LOG_INFO("Running USBDEV test");

  // Call `usbdev_init` here so that DPI will not start until the
  // simulation has finished all of the printing, which takes a while
  // if `--trace` was passed in.
  usbdev_init(&usbdev, /* pinflip= */ false, /* rx_diff= */ false,
              /* tx_diff= */ false);
  usb_controlep_init(&usbdev_control, &usbdev, 0, config_descriptors,
                     sizeof(config_descriptors));
  usb_simpleserial_init(&simple_serial, &usbdev, 1, usb_receipt_callback);

  while (usb_chars_recved_total < kExpectedUsbCharsRecved) {
    usbdev_poll(&usbdev);
  }

  base_printf("\r\n");
  for (int i = 0; i < kExpectedUsbCharsRecved; i++) {
    CHECK(buffer[i] == kExpectedUsbRecved[i],
          "Recieved char #%d mismatched: exp = %x, actual = %x", i,
          kExpectedUsbRecved[i], buffer[i]);
  }
  LOG_INFO("USB recieved %d characters: %s", usb_chars_recved_total, buffer);

  return true;
}
