// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>
#include <stdbool.h>

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/usb_controlep.h"
#include "sw/device/lib/usb_simpleserial.h"
#include "sw/device/lib/usbdev.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// These just for the '/' printout
#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR
#include "usbdev_regs.h"  // Generated.

#define REG32(add) *((volatile uint32_t *)(add))

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

static dif_gpio_t gpio;
static dif_spi_device_t spi;
static dif_uart_t uart;

/**
 * Callbacks for processing USB reciept. The latter increments the
 * recieved character by one, to make them distinct.
 */
static void usb_receipt_callback_0(uint8_t c) {
  c = make_printable(c, '?');
  CHECK(dif_uart_byte_send_polled(&uart, c) == kDifUartOk);
  ++usb_chars_recved_total;
}
static void usb_receipt_callback_1(uint8_t c) {
  c = make_printable(c + 1, '?');
  CHECK(dif_uart_byte_send_polled(&uart, c) == kDifUartOk);
  ++usb_chars_recved_total;
}

/**
 * USB Send String
 *
 * Send a 0 terminated string to the USB one byte at a time.
 * The send byte code will flush the endpoint if needed.
 *
 * @param string Zero terminated string to send.
 * @param ss_ctx Pointer to simple string endpoint context to send through.
 */
static void usb_send_str(const char *string, usb_ss_ctx_t *ss_ctx) {
  for (int i = 0; string[i] != 0; ++i) {
    usb_simpleserial_send_byte(ss_ctx, string[i]);
  }
}

// These GPIO bits control USB PHY configuration
static const uint32_t kPinflipMask = 1;
static const uint32_t kDiffMask = 2;
static const uint32_t kUPhyMask = 4;

int main(int argc, char **argv) {
  CHECK(dif_uart_init(
            (dif_uart_params_t){
                .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR),
            },
            &uart) == kDifUartOk);
  CHECK(dif_uart_configure(&uart, (dif_uart_config_t){
                                      .baudrate = kUartBaudrate,
                                      .clk_freq_hz = kClockFreqPeripheralHz,
                                      .parity_enable = kDifUartToggleDisabled,
                                      .parity = kDifUartParityEven,
                                  }) == kDifUartConfigOk);
  base_uart_stdout(&uart);

  pinmux_init();

  CHECK(dif_spi_device_init(
            (dif_spi_device_params_t){
                .base_addr =
                    mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR),
            },
            &spi) == kDifSpiDeviceOk);
  CHECK(dif_spi_device_configure(
            &spi, (dif_spi_device_config_t){
                      .clock_polarity = kDifSpiDeviceEdgePositive,
                      .data_phase = kDifSpiDeviceEdgeNegative,
                      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
                      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
                      .rx_fifo_timeout = 63,
                      .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
                      .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
                  }) == kDifSpiDeviceOk);

  dif_gpio_params_t gpio_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR),
  };
  CHECK(dif_gpio_init(gpio_params, &gpio) == kDifGpioOk);
  // Enable GPIO: 0-7 and 16 is input; 8-15 is output.
  CHECK(dif_gpio_output_set_enabled_all(&gpio, 0x0ff00) == kDifGpioOk);

  LOG_INFO("Hello, USB!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  demo_gpio_startup(&gpio);

  // Call `usbdev_init` here so that DPI will not start until the
  // simulation has finished all of the printing, which takes a while
  // if `--trace` was passed in.
  uint32_t gpio_state;
  CHECK(dif_gpio_read_all(&gpio, &gpio_state) == kDifGpioOk);
  bool pinflip = gpio_state & kPinflipMask ? true : false;
  bool differential = gpio_state & kDiffMask ? true : false;
  bool uphy = gpio_state & kUPhyMask ? true : false;
  LOG_INFO("PHY settings: pinflip=%d differential=%d USB Phy=%d", pinflip,
           differential, uphy);
  // The TI phy always uses single ended TX
  usbdev_init(&usbdev, pinflip, differential, differential && !uphy);

  usb_controlep_init(&usbdev_control, &usbdev, 0, config_descriptors,
                     sizeof(config_descriptors));
  usb_simpleserial_init(&simple_serial0, &usbdev, 1, usb_receipt_callback_0);
  usb_simpleserial_init(&simple_serial1, &usbdev, 2, usb_receipt_callback_1);

  CHECK(dif_spi_device_send(&spi, "SPI!", 4, /*bytes_sent=*/NULL) ==
        kDifSpiDeviceOk);

  bool say_hello = true;
  bool pass_signaled = false;
  while (true) {
    usbdev_poll(&usbdev);

    gpio_state = demo_gpio_to_log_echo(&gpio, gpio_state);
    demo_spi_to_log_echo(&spi);

    while (true) {
      size_t chars_available;
      if (dif_uart_rx_bytes_available(&uart, &chars_available) != kDifUartOk ||
          chars_available == 0) {
        break;
      }

      uint8_t rcv_char;
      CHECK(dif_uart_bytes_receive(&uart, 1, &rcv_char, NULL) == kDifUartOk);
      CHECK(dif_uart_byte_send_polled(&uart, rcv_char) == kDifUartOk);

      CHECK(dif_gpio_write_all(&gpio, rcv_char << 8) == kDifGpioOk);

      if (rcv_char == '/') {
        uint32_t usb_irq_state =
            REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET);
        uint32_t usb_stat = REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET);
        LOG_INFO("I%4x-%8x", usb_irq_state, usb_stat);
      } else {
        usb_simpleserial_send_byte(&simple_serial0, rcv_char);
        usb_simpleserial_send_byte(&simple_serial1, rcv_char + 1);
      }
    }
    if (say_hello && usb_chars_recved_total > 2) {
      usb_send_str("Hello USB World!!!!", &simple_serial0);
      say_hello = false;
    }
    // Signal that the simulation succeeded.
    if (usb_chars_recved_total >= kExpectedUsbCharsRecved && !pass_signaled) {
      LOG_INFO("PASS!");
      pass_signaled = true;
    }
  }

  LOG_INFO("USB recieved %d characters.", usb_chars_recved_total);
}
