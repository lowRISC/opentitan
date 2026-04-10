// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/alert.h"
#include "sw/device/lib/crypto/impl/status.h"

/**
 * Basic mock of the alert driver.
 *
 * Enables on-host unit tests of code that interacts with the alert handler
 * or sensor control registers.
 */

namespace test {
extern "C" {

/**
 * Base mock implementation of read_alert_registers.
 *
 * @return 0, indicating no alerts.
 */
uint32_t read_alert_registers(void) { return 0; }

/**
 * Basic mock implementation of init_alert_registers.
 *
 * @return OK, a successful clearing of all alerts.
 */
status_t init_alert_registers(void) { return OTCRYPTO_OK; }

}  // extern "C"
}  // namespace test
