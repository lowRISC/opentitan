// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SYSRST_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SYSRST_CTRL_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"

/**
 * Setup the sysrst_ctrl direct IO (DIO) pins, that is flash write protect (WP)
 * and EC reset.
 *
 * This function will try to setup the DIO pins as open drain. If this fails,
 * it will then try virtual open drain.
 *
 * This function will panic on error.
 *
 * @param pinmux Pointer to an initialized pinmux DIF.
 */
void sysrst_ctrl_testutils_setup_dio(dif_pinmux_t *pinmux);

/**
 * Release the flash WP and EC reset so that the output is not overidden to low
 * by the block.
 *
 * This function will panic on error.
 *
 * @param pinmux Pointer to an initialized sysrst_ctrl DIF.
 * @param release_ec Whether to release the EC reset pin.
 * @param release_flash Whether to release the flast write protect pin.
 */
void sysrst_ctrl_testutils_release_dio(dif_sysrst_ctrl_t *sysrst_ctrl,
                                       bool release_ec, bool release_flash);

/**
 * Set the EC reset pulse width.
 *
 * The supplied pulse width is converted into a count of AON clock ticks.
 * If the width is not an exact multiple of the AON clock period, the conversion
 * rounds down. The function will panic if the converted pulse width does not
 * fit into the RST_CTL register.
 *
 * @param pinmux Pointer to an initialized sysrst_ctrl DIF.
 * @param pulse_us Pulse width in microseconds.
 */
void sysrst_ctrl_testutils_set_ec_rst_pulse_width(
    dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t pulse_us);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SYSRST_CTRL_TESTUTILS_H_
