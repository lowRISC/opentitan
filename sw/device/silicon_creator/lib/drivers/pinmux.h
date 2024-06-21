// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_

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
 * Configure Schmitt triggers on pinmux MIO and DIO pads as specified by the OTP
 * configuration.
 */
void pinmux_configure_schmitt(void);

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

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
