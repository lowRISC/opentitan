// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_EXAMPLES_DEMOS_H_
#define OPENTITAN_SW_DEVICE_EXAMPLES_DEMOS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"

/**
 * This header provides a small library of reuseable demos for use with
 * OpenTitan example code.
 */

/**
 * The GPIO instances of the demos.
 *
 * Each GPIO pin reaches a single pad, so the four LEDs (IOR10-IOR13) are on
 * gpio1 and the four switches (IOB6, IOB9, IOB10, IOR1) are spread over gpio0
 * and gpio1.
 */
typedef struct demo_gpio {
  dif_gpio_t gpio0;
  dif_gpio_t gpio1;
} demo_gpio_t;

/**
 * Initializes both GPIO instances, connects the LEDs and switches in the
 * pinmux and enables the LED outputs.
 *
 * @param pinmux the pinmux device.
 * @param gpio the GPIO instances to initialize.
 */
void demo_gpio_init(const dif_pinmux_t *pinmux, demo_gpio_t *gpio);

/**
 * Reads the switches.
 *
 * @param gpio the GPIO instances.
 * @return switches 0-3 in bits [3:0], the FTDI bit (SW strap 0) in bit [4].
 */
uint32_t demo_gpio_read(demo_gpio_t *gpio);

/**
 * Sets the four LEDs to the lower nibble of a value.
 *
 * @param gpio the GPIO instances.
 * @param value the value to show.
 */
void demo_gpio_leds_write(demo_gpio_t *gpio, uint32_t value);

/**
 * Runs a small demo on the GPIO pins to show that things are working.
 *
 * @param gpio the GPIO instances to actuate.
 */
void demo_gpio_startup(demo_gpio_t *gpio);

/**
 * Executes a step of a GPIO -> LOG echo demo, by diffing
 * the previous GPIO state with the current state, and reporting
 * the difference.
 *
 * The new state is returned, so it can be passed in on the next
 * iteration.
 *
 * @param gpio the GPIO instances to pull bits from.
 * @param prev_gpio_state the previous GPIO state to diff against.
 * @return the new GPIO state, as returned by `demo_gpio_read()`.
 */
uint32_t demo_gpio_to_log_echo(demo_gpio_t *gpio, uint32_t prev_gpio_state);

/**
 * Attempts to read characters from UART and immediately echo them back,
 * as well as to show their lower nibble on the LEDs.
 *
 * @param uart the UART device to actuate.
 * @param gpio the GPIO instances to actuate.
 */
void demo_uart_to_uart_and_gpio_echo(dif_uart_t *uart, demo_gpio_t *gpio);

#endif  // OPENTITAN_SW_DEVICE_EXAMPLES_DEMOS_H_
