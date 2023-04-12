// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_PWRMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_PWRMGR_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"

/**
 * Set the device in low power mode.
 *
 * A WFI instruction needs to be separately run by the processor to actually
 * enter low power.
 *
 * @param pwrmgr A power manager handle.
 * @param wakeups The bit mask of wakeup requestors.
 * @param domain_config The bit mask for configuring the clock and power
 * domains.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t pwrmgr_testutils_enable_low_power(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_request_sources_t wakeups,
    dif_pwrmgr_domain_config_t domain_config);

/**
 * Determines if the wakeup reasons is as given.
 *
 * @param pwrmgr A power manager handle.
 * @param reasons A bit mask of reasons.
 * @return `kOk(res)` where `res` is true when wakeup reasons matches with
 * `reasons`, otherwise `kInternal`.
 */
OT_WARN_UNUSED_RESULT
status_t pwrmgr_testutils_is_wakeup_reason(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_request_sources_t reasons);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_PWRMGR_TESTUTILS_H_
