// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_ROM_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_ROM_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * ROM read FI test.
 *
 * Read the ROM digest while injecting faults.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_rom_fi_init(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the Rom FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_rom_fi_init(ujson_t *uj);

/**
 * Rom FI command handler.
 *
 * Command handler for the Rom FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_rom_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_ROM_FI_H_
