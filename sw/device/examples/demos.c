// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/demos.h"

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

void demo_gpio_startup(dif_gpio_t *gpio) {
  LOG_INFO("Watch the LEDs!");

  // Give a LED pattern as startup indicator for 5 seconds.
  CHECK_DIF_OK(dif_gpio_write_all(gpio, 0x00ff));
  for (dif_gpio_pin_t i = 0; i < 32; ++i) {
    busy_spin_micros(5 * 1000);  // 5 ms
    CHECK_DIF_OK(dif_gpio_write(gpio, 8 + (i % 8), (i / 8) % 2));
  }
  CHECK_DIF_OK(dif_gpio_write_all(gpio, 0x0000));  // All LEDs off.
}

/**
 * Mask for "valid" GPIO bits. The nibble at [11:8] represents switch inputs,
 * while the bit at [22] represents the FTDI bit (SW strap 0).
 */
static const uint32_t kGpioMask = 0x400f00;

/**
 * Mask for the FTDI bit (SW strap 0) among the GPIO bits.
 */
static const uint32_t kFtdiMask = 0x400000;

uint32_t demo_gpio_to_log_echo(dif_gpio_t *gpio, uint32_t prev_gpio_state) {
  uint32_t gpio_state;
  CHECK_DIF_OK(dif_gpio_read_all(gpio, &gpio_state));
  gpio_state &= kGpioMask;

  uint32_t state_delta = prev_gpio_state ^ gpio_state;
  for (int bit_idx = 0; bit_idx < 8; ++bit_idx) {
    bool changed = ((state_delta >> bit_idx) & 0x1) != 0;
    bool is_currently_set = ((gpio_state >> bit_idx) & 0x1) != 0;
    if (changed) {
      LOG_INFO("GPIO switch #%d changed to %d", bit_idx, is_currently_set);
    }
  }

  if ((state_delta & kFtdiMask) != 0) {
    if ((gpio_state & kFtdiMask) != 0) {
      LOG_INFO("FTDI control changed. Enable JTAG.");
    } else {
      LOG_INFO("FTDI control changed. Enable JTAG.");
    }
  }

  return gpio_state;
}

void demo_spi_to_log_echo(dif_spi_device_handle_t *spi) {
  uint32_t spi_buf[8];
  size_t spi_len;
  CHECK_DIF_OK(dif_spi_device_recv(spi, spi_buf, sizeof(spi_buf), &spi_len));
  if (spi_len > 0) {
    uint32_t echo_word = spi_buf[0] ^ 0x01010101;
    CHECK_DIF_OK(dif_spi_device_send(spi, &echo_word, sizeof(uint32_t),
                                     /*bytes_sent=*/NULL));
    LOG_INFO("SPI: %!s", spi_len, spi_buf);
  }
}

void demo_uart_to_uart_and_gpio_echo(dif_uart_t *uart, dif_gpio_t *gpio) {
  while (true) {
    size_t chars_available;
    if (dif_uart_rx_bytes_available(uart, &chars_available) != kDifOk ||
        chars_available == 0) {
      break;
    }

    uint8_t rcv_char;
    CHECK_DIF_OK(dif_uart_bytes_receive(uart, 1, &rcv_char, NULL));
    CHECK_DIF_OK(dif_uart_byte_send_polled(uart, rcv_char));
    CHECK_DIF_OK(dif_gpio_write_all(gpio, rcv_char));
  }
}
