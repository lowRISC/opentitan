// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SYSRST_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SYSRST_CTRL_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"

/**
 * Setup the sysrst_ctrl direct IO (DIO) pins, that is flash write protect (WP)
 * and EC reset. Also disable the EC reset debounce timer and release the flash
 * WP so that the output is not overidden to low by the block.
 *
 * This function will try to setup the DIO pins as open drain. If this fails,
 * it will then try virtual open drain.
 *
 * This function will panic on error.
 *
 * @param pinmux Pointer to an initialized pinmux DIF.
 * @param pinmux Pointer to an initialized sysrst_ctrl DIF.
 */
void setup_dio_pins(dif_pinmux_t *pinmux, dif_sysrst_ctrl_t *sysrst_ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SYSRST_CTRL_TESTUTILS_H_
