// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"

/**
 * Default pinmux initialization.
 *
 * Initializes GPIOs to map to the lowest-numbered MIOs, except where it
 * conflicts with UARTs. Then initializes 2 UART mappings to (IOC3,IOC8) and
 * (IOC4,IOC9), denoted as (RX pin,TX pin).
 *
 * Also ensures IOR0 and IOR1 outputs are disabled, for use as USB sense inputs.
 *
 * This function is specific to top_earlgrey and top_englishbreakfast.
 */
void pinmux_testutils_init(dif_pinmux_t *pinmux);

/**
 * Maps the chip IOs to the GPIO peripheral in input and output directions.
 */
extern const dif_pinmux_index_t kPinmuxTestutilsGpioInselPins[kDifGpioNumPins];
extern const dif_pinmux_index_t kPinmuxTestutilsGpioMioOutPins[kDifGpioNumPins];

/**
 * Returns the mask of testable GPIO pins.
 *
 * Returns a simulation-device-specific mask that enables testing of only a
 * subset of GPIOs depending on the IO allocation limitations.
 */
uint32_t pinmux_testutils_get_testable_gpios_mask(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_
