// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_LC_CTRL_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_LC_CTRL_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Initializes the trigger and configures the device for the LC CTRL FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_lc_ctrl_fi_init(ujson_t *uj);

/**
 * lc_ctrl.runtime_corruption command handler.
 *
 * Try to manipulate the LC state and counter using FI.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_lc_ctrl_fi_runtime_corruption(ujson_t *uj);

/**
 * LC CTRL FI command handler.
 *
 * Command handler for the LC CTRL FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_lc_ctrl_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_LC_CTRL_FI_H_
