// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ALERT_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ALERT_H_

#include <stdint.h>

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * Read the alert, the sensors, and the local alert registers.
 *
 * @return The OR of the alerts, sensors, and local alerts.
 * Zero means no alerts were triggered.
 */
OT_WARN_UNUSED_RESULT
uint32_t read_alert_registers(void);

/**
 * Clear the class alerts accumulators.
 *
 * @return OK when the alert accumulators are cleared.
 */
OT_WARN_UNUSED_RESULT
status_t clear_alert_class_accum(void);

/**
 * Clear the alert, the sensors, and the local alert registers.
 *
 * @return OK when the alerts are cleared.
 */
OT_WARN_UNUSED_RESULT
status_t init_alert_registers(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ALERT_H_
