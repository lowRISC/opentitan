// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RET_SRAM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RET_SRAM_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"

/**
 * Clears the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..3].
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_clear(size_t counter);

/**
 * Returns the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..3].
 * @param[out] Value of the counter.
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_get(size_t counter, uint32_t *value);

/**
 * Increments the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..3].
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_increment(size_t counter);

/**
 * Sets the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..3].
 * @param Value of the counter.
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_set(size_t counter, uint32_t value);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RET_SRAM_TESTUTILS_H_
