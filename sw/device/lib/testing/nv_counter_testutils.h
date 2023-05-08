// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_NV_COUNTER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_NV_COUNTER_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

/**
 * Returns the value of a non-volatile counter in flash.
 *
 * @param counter Counter ID, [0, 2].
 * @value[out] Value of the non-volatile counter
 * @return the result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_counter_get(size_t counter, uint32_t *value);

/**
 * Increments a non-volatile counter in flash.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param counter Counter ID, [0, 2].
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_counter_increment(
    dif_flash_ctrl_state_t *flash_state, size_t counter);

/**
 * Sets a non-volatile counter to at least `val`.
 *
 * This function simply writes zeros to the corresponding flash word without any
 * checks and is intended for contexts where performance is critical, e.g. ISRs.
 * The value of the counter will not change if it is already greater than or
 * equal to `val`.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param counter Counter ID, [0, 2].
 * @param val Counter value.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_counter_set_at_least(
    dif_flash_ctrl_state_t *flash_state, size_t counter, uint32_t val);

/**
 * Sets a strike counter to an arbitrary value.
 *
 * If the arbitrary value is impossible (attempts to flip a bit
 * from 0 to 1 without an erase), an error is created.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param strike_counter The address of the counter.
 * @param new_val The new counter value.
 * @return The result of the operation.
 */
void flash_ctrl_testutils_set_counter(dif_flash_ctrl_state_t *flash_state,
                                      uint32_t *strike_counter,
                                      uint32_t new_val);

/**
 * At the beginning of the simulation (Verilator, VCS,etc.),
 * the content of the flash might be all-zeros, and thus,
 * the NVM counter's inital value might be 256.
 * In that case, flash_ctrl_testutils_counter_set_at_least() will not increment
 * This function can be used to initialize a NVM counter to zero by filling
 * its flash region with non-zero values.
 *
 * @param flash_state A flash_ctrl handle.
 * @param counter The ID of the NVM counter, [0, 2].
 * @param The result of the operation.
 **/
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_counter_init_zero(
    dif_flash_ctrl_state_t *flash_state, size_t counter);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_NV_COUNTER_TESTUTILS_H_
