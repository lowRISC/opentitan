// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTP_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTP_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Otp HW Cfg FI test.
 *
 * Tests whether a fault into the HW CFG partition is possible.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otp_fi_hw_cfg(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the Otp FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otp_fi_init(ujson_t *uj);

/**
 * Otp LC FI test.
 *
 * Tests whether a fault into the LifeCycle partition is possible.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otp_fi_life_cycle(ujson_t *uj);

/**
 * Otp SW Cfg FI test.
 *
 * Tests whether a fault into the SW CFG partition is possible.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otp_fi_owner_sw_cfg(ujson_t *uj);

/**
 * Otp Vendor FI test.
 *
 * Tests whether a fault into the vendor partition is possible.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otp_fi_vendor_test(ujson_t *uj);

/**
 * Otp FI command handler.
 *
 * Command handler for the Otp FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otp_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTP_FI_H_
