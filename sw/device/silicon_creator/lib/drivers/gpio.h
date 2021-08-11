// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_GPIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_GPIO_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Read the value of all 32 GPIO pins.
 *
 * The least significant bit in the returned value is index 0, the
 * most significant bit is index 31.
 *
 * The pinmux must be configured to connect GPIO pins to MIO pads,
 * see the pinmux driver for the configuration details.
 * Unconnected pins will be set to 0.
 *
 * @return The `DATA_IN` value for the GPIO pins.
 */
uint32_t gpio_read(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_GPIO_H_
