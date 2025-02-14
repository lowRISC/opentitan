// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Driver for the Pin Multiplexer (pinmux).
 *
 * The pinmux connects peripheral input and output signals to the Padring
 * MIO pad input and output signals.
 */

/**
 * Initialize the pinmux with the configuration required for the ROM.
 */
void pinmux_init(void);

/**
 * Initialize the pinmux with output UART0 only.
 */
void pinmux_init_uart0_tx(void);

/**
 * Sets the input pad for the specified peripheral input.
 *
 * @param periph A peripheral input (e.g. top_earlgrey_pinmux_peripheral_in_t
 * periph).
 * @param insel An MIO pad to link it to (e.g. top_earlgrey_pinmux_insel_t
 * insel).
 */
void pinmux_configure_input(uint32_t periph, uint32_t insel);

/**
 * Enables or disables pull-up/pull-down for the specified pad.
 *
 * @param pad A MIO pad (e.g. top_earlgrey_muxed_pads_t).
 * @param enable Whether the internal pull resistor should be enabled.
 * @param up Whether the pull resistor should pull up(true) or down(false).
 */
void pinmux_enable_pull(uint32_t pad, bool enable, bool up);

/**
 * Read the SW_STRAP value.
 *
 * The straping value is encoded with two bits per pin and encodes the
 * strength of the external pull resistors in the returned value.
 *
 * Each 2-bit field encodes the following values:
 * - 0: Strong pull down
 * - 1: Weak pull down
 * - 2: Weak pull up
 * - 3: Strong pull up
 *
 * The values of the 3 strapping pins are concatenated together, yielding a
 * 6-bit strapping value.
 *
 * @return The strapping value 0-63.
 */
uint32_t pinmux_read_straps(void);

/**
 * Initialize the USB sense pin.
 *
 * This connects the UsbdevSense input to InselConstantOne.
 */
void pinmux_init_usb(void);

/**
 * Read the value of a GPIO
 *
 * @param gpio The GPIO to read.
 * @return The value read.
 */
bool pinmux_read_gpio(uint32_t gpio);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
