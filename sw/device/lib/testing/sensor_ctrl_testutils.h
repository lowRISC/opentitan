// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SENSOR_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SENSOR_CTRL_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_sensor_ctrl.h"

/**
 * Returns true if ast_init is done.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @return True is ast_init is done.
 */
bool sensor_ctrl_ast_init_done(const dif_sensor_ctrl_t *sensor_ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SENSOR_CTRL_TESTUTILS_H_
