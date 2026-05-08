// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_BOOT_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_BOOT_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Invalidates the signatures of the inactive BL0 slot.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_inactive_firmware_invalidation(ujson_t *uj);

/**
 * Sets the next boot slot.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_next_boot_slot(ujson_t *uj);

/**
 * Get the status of the boot, namely which slots are filled.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_boot_status(ujson_t *uj);

/**
 * Get the status of the epmp, namely which entries are set.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_epmp_status(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the Boot FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_boot_fi_init(ujson_t *uj);

/**
 * Boot FI command handler.
 *
 * Command handler for the Boot FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_boot_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_BOOT_FI_H_
