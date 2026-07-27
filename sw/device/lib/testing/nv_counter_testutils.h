// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_NV_COUNTER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_NV_COUNTER_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"

/**
 * Returns the value of a non-volatile counter in flash.
 *
 * @param counter Counter ID, [0, 2].
 * @param[out] Value of the non-volatile counter
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nv_counter_testutils_counter_get(size_t counter, uint32_t *value);

/**
 * Increments a non-volatile counter in flash.
 *
 * @param counter Counter ID, [0, 2].
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nv_counter_testutils_counter_increment(size_t counter);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_NV_COUNTER_TESTUTILS_H_
