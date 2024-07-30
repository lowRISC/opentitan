// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_EXTCLK_SCA_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_EXTCLK_SCA_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Extclk configure command handler.
 *
 * Allows to configure the external clock.
 * The uJSON data contains:
 *  - sel: External clock on or off.
 *  - hi_speed_sel: Nominal or low-speed external clock.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_extclk_sca_fi_configure(ujson_t *uj);

/**
 * EXTCLK SCA FI command handler.
 *
 * Command handler for the EXTCLK SCA FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_extclk_sca_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_EXTCLK_SCA_FI_H_
