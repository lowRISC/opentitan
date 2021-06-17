// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_WATCHDOG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_WATCHDOG_H_
#include <stdint.h>

/**
 * Initialize the watchdog timer.
 *
 * @param timeout_ms The timeout, in milliseconds, after which the watchdog
 *                   will trigger a reset.
 */
void watchdog_init(uint32_t timeout_ms);

/**
 * Pet the watchdog, thus preventing a watchdog initiated reset.
 */
void watchdog_pet(void);

/**
 * Get the current watchdog counter value.
 */
uint32_t watchdog_get(void);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_WATCHDOG_H_
