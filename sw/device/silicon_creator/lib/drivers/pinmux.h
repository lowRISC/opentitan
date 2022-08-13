// Copyright lowRISC contributors.
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

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
