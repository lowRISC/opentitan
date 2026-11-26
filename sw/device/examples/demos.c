// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/demos.h"

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  /**
   * gpio1 pins 25-28 drive the LED pads IOR10-IOR13.
   */
  kLedPin0 = 25,
  kLedCount = 4,
  /**
   * gpio1 pin 2 reads SW strap 0 (IOC0), the FTDI bit.
   */
  kFtdiPin = 2,
  /**
   * Position of the FTDI bit in the state returned by `demo_gpio_read()`.
   */
  kFtdiBit = 4,
};

static const uint32_t kLedMask = ((1u << kLedCount) - 1) << kLedPin0;

/**
 * A switch, read through the GPIO pin that connets to its pad.
 */
typedef struct demo_switch {
  bool on_gpio1;
  dif_gpio_pin_t pin;
  top_earlgrey_pinmux_peripheral_in_t periph;
  top_earlgrey_pinmux_insel_t insel;
} demo_switch_t;

static const demo_switch_t kSwitches[] = {
    {false, 27, kTopEarlgreyPinmuxPeripheralInGpio0Gpio27,
     kTopEarlgreyPinmuxInselIob6},
    {false, 30, kTopEarlgreyPinmuxPeripheralInGpio0Gpio30,
     kTopEarlgreyPinmuxInselIob9},
    {false, 31, kTopEarlgreyPinmuxPeripheralInGpio0Gpio31,
     kTopEarlgreyPinmuxInselIob10},
    {true, 16, kTopEarlgreyPinmuxPeripheralInGpio1Gpio16,
     kTopEarlgreyPinmuxInselIor1},
};

void demo_gpio_init(const dif_pinmux_t *pinmux, demo_gpio_t *gpio) {
  CHECK_DIF_OK(dif_gpio_init(
      mmio_region_from_addr(TOP_EARLGREY_GPIO0_BASE_ADDR), &gpio->gpio0));
  CHECK_DIF_OK(dif_gpio_init(
      mmio_region_from_addr(TOP_EARLGREY_GPIO1_BASE_ADDR), &gpio->gpio1));
  for (uint32_t i = 0; i < kLedCount; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor10 + i,
                                 kTopEarlgreyPinmuxOutselGpio1Gpio25 + i));
  }
  for (size_t i = 0; i < ARRAYSIZE(kSwitches); ++i) {
    CHECK_DIF_OK(dif_pinmux_input_select(pinmux, kSwitches[i].periph,
                                         kSwitches[i].insel));
  }
  CHECK_DIF_OK(
      dif_gpio_output_set_enabled_masked(&gpio->gpio1, kLedMask, kLedMask));
}

uint32_t demo_gpio_read(demo_gpio_t *gpio) {
  uint32_t state = 0;
  for (size_t i = 0; i < ARRAYSIZE(kSwitches); ++i) {
    bool value;
    CHECK_DIF_OK(
        dif_gpio_read(kSwitches[i].on_gpio1 ? &gpio->gpio1 : &gpio->gpio0,
                      kSwitches[i].pin, &value));
    state |= (uint32_t)value << i;
  }
  bool ftdi;
  CHECK_DIF_OK(dif_gpio_read(&gpio->gpio1, kFtdiPin, &ftdi));
  return state | (uint32_t)ftdi << kFtdiBit;
}

void demo_gpio_leds_write(demo_gpio_t *gpio, uint32_t value) {
  CHECK_DIF_OK(dif_gpio_write_masked(&gpio->gpio1, kLedMask,
                                     (value << kLedPin0) & kLedMask));
}

void demo_gpio_startup(demo_gpio_t *gpio) {
  LOG_INFO("Watch the LEDs!");

  // Give a LED pattern as startup indicator.
  demo_gpio_leds_write(gpio, 0xf);
  for (dif_gpio_pin_t i = 0; i < 4 * kLedCount; ++i) {
    busy_spin_micros(5 * 1000);  // 5 ms
    CHECK_DIF_OK(dif_gpio_write(&gpio->gpio1, kLedPin0 + (i % kLedCount),
                                (i / kLedCount) % 2));
  }
  demo_gpio_leds_write(gpio, 0);  // All LEDs off.
}

uint32_t demo_gpio_to_log_echo(demo_gpio_t *gpio, uint32_t prev_gpio_state) {
  uint32_t gpio_state = demo_gpio_read(gpio);

  uint32_t state_delta = prev_gpio_state ^ gpio_state;
  for (size_t bit_idx = 0; bit_idx < ARRAYSIZE(kSwitches); ++bit_idx) {
    bool changed = ((state_delta >> bit_idx) & 0x1) != 0;
    bool is_currently_set = ((gpio_state >> bit_idx) & 0x1) != 0;
    if (changed) {
      LOG_INFO("GPIO switch #%d changed to %d", (int)bit_idx, is_currently_set);
    }
  }

  if ((state_delta >> kFtdiBit) & 0x1) {
    LOG_INFO("FTDI control changed. Enable JTAG.");
  }

  return gpio_state;
}

void demo_uart_to_uart_and_gpio_echo(dif_uart_t *uart, demo_gpio_t *gpio) {
  while (true) {
    size_t chars_available;
    if (dif_uart_rx_bytes_available(uart, &chars_available) != kDifOk ||
        chars_available == 0) {
      break;
    }

    uint8_t rcv_char;
    CHECK_DIF_OK(dif_uart_bytes_receive(uart, 1, &rcv_char, NULL));
    CHECK_DIF_OK(dif_uart_byte_send_polled(uart, rcv_char));
    demo_gpio_leds_write(gpio, rcv_char);
  }
}
