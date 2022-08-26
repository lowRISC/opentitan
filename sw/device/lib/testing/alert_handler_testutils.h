// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ALERT_HANDLER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ALERT_HANDLER_TESTUTILS_H_

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_base.h"

/**
 * Configures alert handler with all required runtime information.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset. If `locked` is set to
 * `kDifToggleEnabled`, then every lockable configuration will be locked.
 * Otherwise, configurations may only be locked by performing subsequent calls
 * to each component-specific locking DIF: `dif_alert_handler_lock_*(...)`.
 *
 * @param alert_handler An alert handler handle.
 * @param config Runtime configuration parameters.
 * @param locked The locked state to set for each configuration.
 */
void alert_handler_testutils_configure_all(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_config_t config,
    dif_toggle_t locked);

/**
 * Returns the number of cycles corresponding to the given microseconds.
 */
uint32_t alert_handler_testutils_get_cycles_from_us(uint64_t microseconds);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ALERT_HANDLER_TESTUTILS_H_
