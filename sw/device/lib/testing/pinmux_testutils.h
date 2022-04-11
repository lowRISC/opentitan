// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_

#include <stdint.h>

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

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_
