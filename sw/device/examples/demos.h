// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_EXAMPLES_DEMOS_H_
#define OPENTITAN_SW_DEVICE_EXAMPLES_DEMOS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"

/**
 * This header provides a small library of reuseable demos for use with
 * OpenTitan example code.
 */

/**
 * Runs a small demo on the GPIO pins to show that things are working.
 *
 * @param gpio the GPIO device to actuate.
 */
void demo_gpio_startup(dif_gpio_t *gpio);

/**
 * Executes a step of a GPIO -> LOG echo demo, by diffing
 * the previous GPIO state with the current state, and reporting
 * the difference.
 *
 * The new state is returned, so it can be passed in on the next
 * iteration.
 *
 * @param gpio the GPIO device to pull bits from.
 * @param prev_gpio_state the previous GPIO state to diff against.
 * @return the new GPIO state.
 */
uint32_t demo_gpio_to_log_echo(dif_gpio_t *gpio, uint32_t prev_gpio_state);

/**
 * Attempts to read at most 32 bytes from SPI, and echo them as printable
 * characters to LOG.
 */
void demo_spi_to_log_echo(const dif_spi_device_t *spi);

/**
 * Attempts to read characters from UART and immediately echo them back,
 * as well as to write its bits to GPIO pins 8-15.
 *
 * @param uart the UART device to actuate.
 * @param gpio the GPIO device to actuate.
 */
void demo_uart_to_uart_and_gpio_echo(dif_uart_t *uart, dif_gpio_t *gpio);

#endif  // OPENTITAN_SW_DEVICE_EXAMPLES_DEMOS_H_
