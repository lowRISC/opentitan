// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>
#include <stdbool.h>

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/usb_testutils.h"
#include "sw/device/lib/testing/usb_testutils_controlep.h"
#include "sw/device/lib/testing/usb_testutils_simpleserial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// These just for the '/' printout
#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR
#include "usbdev_regs.h"  // Generated.

#define REG32(add) *((volatile uint32_t *)(add))

OTTF_DEFINE_TEST_CONFIG();

/**
 * Configuration values for USB.
 */
static uint8_t config_descriptors[] = {
    USB_CFG_DSCR_HEAD(
        USB_CFG_DSCR_LEN + 2 * (USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN),
        2),
    VEND_INTERFACE_DSCR(0, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 1, 32, 0),
    USB_BULK_EP_DSCR(1, 1, 32, 4),
    VEND_INTERFACE_DSCR(1, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 2, 32, 0),
    USB_BULK_EP_DSCR(1, 2, 32, 4),
};

/**
 * USB device context types.
 */
static usb_testutils_ctx_t usbdev;
static usb_testutils_controlep_ctx_t usbdev_control;
static usb_testutils_ss_ctx_t simple_serial0;
static usb_testutils_ss_ctx_t simple_serial1;

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
static dif_pinmux_t pinmux;
static dif_spi_device_handle_t spi;
static dif_uart_t uart;

/**
 * Callbacks for processing USB reciept. The latter increments the
 * recieved character by one, to make them distinct.
 */
static void usb_receipt_callback_0(uint8_t c) {
  c = make_printable(c, '?');
  CHECK_DIF_OK(dif_uart_byte_send_polled(&uart, c));
  ++usb_chars_recved_total;
}
static void usb_receipt_callback_1(uint8_t c) {
  c = make_printable(c + 1, '?');
  CHECK_DIF_OK(dif_uart_byte_send_polled(&uart, c));
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
static void usb_send_str(const char *string, usb_testutils_ss_ctx_t *ss_ctx) {
  for (int i = 0; string[i] != 0; ++i) {
    CHECK_STATUS_OK(usb_testutils_simpleserial_send_byte(ss_ctx, string[i]));
  }
}

// These GPIO bits control USB PHY configuration
static const uint32_t kPinflipMask = (1 << 8);
static const uint32_t kDiffXcvrMask = (1 << 9);
static const uint32_t kUPhyMask = (1 << 10);

static dif_pinmux_index_t leds[] = {
    kTopEarlgreyPinmuxMioOutIor10,
    kTopEarlgreyPinmuxMioOutIor11,
    kTopEarlgreyPinmuxMioOutIor12,
    kTopEarlgreyPinmuxMioOutIor13,
};

static dif_pinmux_index_t switches[] = {
    kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob7,
    kTopEarlgreyPinmuxInselIob8,
    kTopEarlgreyPinmuxInselIob9,
};

void configure_pinmux(void) {
  pinmux_testutils_init(&pinmux);
  // Hook up some LEDs.
  for (size_t i = 0; i < ARRAYSIZE(leds); ++i) {
    dif_pinmux_index_t gpio = kTopEarlgreyPinmuxOutselGpioGpio0 + i;
    CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, leds[i], gpio));
  }
  // Hook up DIP switches.
  for (size_t i = 0; i < ARRAYSIZE(switches); ++i) {
    dif_pinmux_index_t gpio = kTopEarlgreyPinmuxPeripheralInGpioGpio8 + i;
    CHECK_DIF_OK(dif_pinmux_input_select(&pinmux, gpio, switches[i]));
  }
}

void _ottf_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  configure_pinmux();

  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                 .parity_enable = kDifToggleDisabled,
                 .parity = kDifUartParityEven,
                 .tx_enable = kDifToggleEnabled,
                 .rx_enable = kDifToggleEnabled,
             }));
  base_uart_stdout(&uart);

  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi));
  dif_spi_device_config_t spi_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModeGeneric,
      .mode_cfg =
          {
              .generic =
                  {
                      .rx_fifo_commit_wait = 63,
                      .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
                      .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
                  },
          },
  };
  CHECK_DIF_OK(dif_spi_device_configure(&spi, spi_config));

  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  // Enable GPIO: 0-7 and 16 is input; 8-15 is output.
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, 0x000ff));

  LOG_INFO("Hello, USB!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  demo_gpio_startup(&gpio);

  // Call `usbdev_init` here so that DPI will not start until the
  // simulation has finished all of the printing, which takes a while
  // if `--trace` was passed in.
  uint32_t gpio_state;
  CHECK_DIF_OK(dif_gpio_read_all(&gpio, &gpio_state));
  bool pinflip = gpio_state & kPinflipMask ? true : false;
  bool differential_xcvr = gpio_state & kDiffXcvrMask ? true : false;
  bool uphy = gpio_state & kUPhyMask ? true : false;
  LOG_INFO("PHY settings: pinflip=%d differential_xcvr=%d USB Phy=%d", pinflip,
           differential_xcvr, uphy);
  // Connect correct VBUS detection pin
  if (uphy) {
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
        kTopEarlgreyPinmuxInselIoc7));
  } else {
    CHECK_DIF_OK(dif_pinmux_input_select(
        &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
        kTopEarlgreyPinmuxInselConstantOne));
  }
  CHECK_DIF_OK(dif_spi_device_send(&spi, "SPI!", 4, /*bytes_sent=*/NULL));

  // The TI phy always uses a differential TX interface
  CHECK_STATUS_OK(usb_testutils_init(&usbdev, pinflip, differential_xcvr,
                                     differential_xcvr && !uphy));

  CHECK_STATUS_OK(usb_testutils_controlep_init(
      &usbdev_control, &usbdev, 0, config_descriptors,
      sizeof(config_descriptors), NULL, 0));

  while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured) {
    CHECK_STATUS_OK(usb_testutils_poll(&usbdev));
  }

  CHECK_STATUS_OK(usb_testutils_simpleserial_init(&simple_serial0, &usbdev, 1,
                                                  usb_receipt_callback_0));
  CHECK_STATUS_OK(usb_testutils_simpleserial_init(&simple_serial1, &usbdev, 2,
                                                  usb_receipt_callback_1));

  bool say_hello = true;
  bool pass_signaled = false;
  while (true) {
    CHECK_STATUS_OK(usb_testutils_poll(&usbdev));

    gpio_state = demo_gpio_to_log_echo(&gpio, gpio_state);
    demo_spi_to_log_echo(&spi);

    while (true) {
      size_t chars_available;
      if (dif_uart_rx_bytes_available(&uart, &chars_available) != kDifOk ||
          chars_available == 0) {
        break;
      }

      uint8_t rcv_char;
      CHECK_DIF_OK(dif_uart_bytes_receive(&uart, 1, &rcv_char, NULL));
      CHECK_DIF_OK(dif_uart_byte_send_polled(&uart, rcv_char));

      CHECK_DIF_OK(dif_gpio_write_all(&gpio, (uint32_t)rcv_char << 8));

      if (rcv_char == '/') {
        uint32_t usb_irq_state =
            REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET);
        uint32_t usb_stat = REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET);
        LOG_INFO("I%04x-%08x", usb_irq_state, usb_stat);
      } else {
        CHECK_STATUS_OK(
            usb_testutils_simpleserial_send_byte(&simple_serial0, rcv_char));
        CHECK_STATUS_OK(usb_testutils_simpleserial_send_byte(&simple_serial1,
                                                             rcv_char + 1));
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
