// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_LIB_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_LIB_H_

#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/json/sca_lib_commands.h"

typedef struct sca_registered_alerts {
  uint32_t alerts_1;
  uint32_t alerts_2;
  uint32_t alerts_3;
} sca_registered_alerts_t;

/**
 * Configures the entropy complex for OTBN tests.
 *
 * Similar to entropy_testutils_auto_mode_init(), this function inits the
 * entropy complex. However, in comparison to the function available in the
 * testutils, this function maximizes the reseed intervall to 0xffffffff.
 * This is necessary to guarantee a fixed trigger window for OTBN tests.
 *
 * @return OK or error.
 */
status_t sca_configure_entropy_source_max_reseed_interval(void);

/**
 * Returns the registered alerts.
 *
 * If a fault injection triggered an alert, this function returns the alert ID
 * back to the host. Afterwards, the alert is cleared.
 *
 * @return A struct containing which of the alerts were triggered during the
 * test.
 */
sca_registered_alerts_t sca_get_triggered_alerts(void);

/**
 * Configures the alert handler for FI.
 *
 * Register all alerts and let them escalate to Phase0 only.
 */
void sca_configure_alert_handler(void);

/**
 * Reads the device ID from the LC.
 *
 * Can be used to categorize different SCA and FI runs.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t sca_read_device_id(ujson_t *uj);

/**
 * Configures CPU for SCA and FI penetration tests.
 *
 * This function disables the iCache and the dummy instructions using the
 * CPU Control and Status Register (cpuctrlsts).
 */
void sca_configure_cpu(void);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_LIB_H_
