// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Initialize CryptoLib command handler.
 *
 * This command is designed to setup the CryptoLib FI firmware.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi_init(ujson_t *uj);

/**
 * CryptoLib FI command handler.
 *
 * Command handler for the CryptoLib FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_cryptolib_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_CRYPTOLIB_FI_H_
