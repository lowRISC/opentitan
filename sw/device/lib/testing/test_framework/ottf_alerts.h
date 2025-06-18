// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ALERTS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ALERTS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"

/**
 * Configure and enable all alerts.
 *
 * Alerts are configured for class D which is configured for signal 0.
 * The ping and IRQ deadline timers are set to their maximums.
 * OTTF is expected to handle the class D IRQ before the alert escalates.
 *
 * The alert handler config is not locked and can be changed by tests.
 *
 * Note that this function enables external IRQs for Ibex.
 */
OT_WARN_UNUSED_RESULT
status_t ottf_alerts_enable_all(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ALERTS_H_
