// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_EDN_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_EDN_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * edn.fi.bus_ack command handler.
 *
 * The goal of this penetration test is to inject a fault into
 * the ACK signal transmitted by the EDN to achieve that the
 * same random word is transmitted multiple times.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_fi_bus_ack(ujson_t *uj);

/**
 * edn.fi.bus_data command handler.
 *
 * The goal of this penetration test is to inject a fault into
 * the EDN when random data is generated and transferred to Ibex.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_fi_bus_data(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the EDN FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_fi_init(ujson_t *uj);

/**
 * EDN FI command handler.
 *
 * Command handler for the EDN FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_edn_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_EDN_FI_H_
