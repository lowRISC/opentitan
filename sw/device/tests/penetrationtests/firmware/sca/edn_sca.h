// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_EDN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_EDN_SCA_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * edn.sca.bus_data command handler.
 *
 * The goal of this penetration test is to capture traces when
 * the EDN generated random data and transfers it to Ibex.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_sca_bus_data(ujson_t *uj);

/**
 * edn.sca.bus_data_batch_fvsr command handler.
 *
 * Batch version of edn.sca.bus_data with FvsR data.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_sca_bus_data_batch_fvsr(ujson_t *uj);

/**
 * edn.sca.bus_data_batch_random command handler.
 *
 * Batch version of edn.sca.bus_data with random data.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_sca_bus_data_batch_random(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the EDN SCA test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_pentest_init(ujson_t *uj);

/**
 * EDN SCA command handler.
 *
 * Command handler for the EDN SCA command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_sca(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_EDN_SCA_H_
