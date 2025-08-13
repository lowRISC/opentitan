// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ALERTS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ALERTS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_alert_handler.h"

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

/**
 * Disable an alert in OTTF's alert catching configuration.
 *
 * Useful when a particular alert cannot be dismissed when caught.
 *
 * @param alert The alert to be ignored.
 */
OT_WARN_UNUSED_RESULT
status_t ottf_alerts_ignore_alert(dif_alert_handler_alert_t alert);

/**
 * Record for the OTTF alert catcher that the given alert is expected.
 *
 * When this alert is caught, OTTF will not fault but will remember that
 * the alert fired. Pair this with `ottf_alerts_expect_alert_finish` to
 * confirm that the expected alert was indeed caught.
 *
 * @param alert The alert that is expected.
 */
OT_WARN_UNUSED_RESULT
status_t ottf_alerts_expect_alert_start(dif_alert_handler_alert_t alert);

/**
 * Finish expecting an alert and confirm that OTTF caught it firing.
 *
 * Must be called after `ottf_alerts_expect_alert_start`. If the alert
 * was not caught while it was expected, an error result will be returned.

 * The alert will no longer be expected after this call, and OTTF will
 * forget that it was caught.
 *
 * @param alert The alert that was expected.
 */
OT_WARN_UNUSED_RESULT
status_t ottf_alerts_expect_alert_finish(dif_alert_handler_alert_t alert);

/**
 * OTTF alert ISR handler.
 *
 * Called when an alert fires on class D when OTTF alert catching is enabled.
 */
void ottf_alert_isr(uint32_t *exc_info);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_ALERTS_H_
