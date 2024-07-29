// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_IBEX_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_IBEX_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * ibex.sca.key_sideloading
 *
 * This SCA penetration test executes the following instructions:
 * - Retrieve salt over UART & feed salt into keymanager
 * - Set trigger
 * - Instruct the keymanager to generate a key based on the salt.
 * - Unset trigger
 * - Read back generated key provided at the SW interface of the keymanager.
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca_key_sideloading(ujson_t *uj);

/**
 * ibex.sca.tl_write
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write data over TL-UL into SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca_tl_write(ujson_t *uj);

/**
 * ibex.sca.tl_read
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca_tl_read(ujson_t *uj);

/**
 * ibex.sca.register_file_write
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write provided data to registers in RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca_register_file_write(ujson_t *uj);

/**
 * ibex.sca.register_file_read
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca_register_file_read(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the Ibex SCA test.
 *
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca_init(ujson_t *uj);

/**
 * Ibex SCA command handler.
 *
 * Command handler for the Ibex SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_IBEX_SCA_H_
