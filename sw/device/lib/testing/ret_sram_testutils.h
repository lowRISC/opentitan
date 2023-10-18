// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RET_SRAM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RET_SRAM_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"

/**
 * This provides a number of counters and a scratch array.
 * They will be preserved across reset, and cleared on POR.
 *
 * All data read must be initialized, or ECC errors will be triggered.
 */
enum {
  /**
   * The number of 32-bit counters.
   */
  kRetSramTestutilsNumberOfCounters = 4,

  /**
   * The size of the scratch array in 32-bit words.
   */
  kRetSramTestutilsScratchSizeAsInts = 256
};

/**
 * Clears the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..kRetSramTestutilsNumberOfCounters].
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_clear(size_t counter);

/**
 * Returns the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..kRetSramTestutilsNumberOfCounters].
 * @param[out] Value of the counter.
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_get(size_t counter, uint32_t *value);

/**
 * Increments the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..kRetSramTestutilsNumberOfCounters].
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_increment(size_t counter);

/**
 * Sets the value of a counter in retention sram.
 *
 * @param counter Counter ID, [0..kRetSramTestutilsNumberOfCounters].
 * @param Value of the counter.
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_counter_set(size_t counter, uint32_t value);

/**
 * Read data from the scratch array.
 *
 * @param offset The starting offset to be read as int32s.
 * @param size Number of uint32 words to be read.
 * @param[out] dest Where to place the data read.
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_scratch_read(size_t offset, size_t size,
                                         uint32_t *dest);

/**
 * Write data to the scratch array.
 *
 * @param offset The starting offset to be written as int32s.
 * @param size Number of uint32 words to be written.
 * @param src The address of the data to be written.
 * @return The status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t ret_sram_testutils_scratch_write(size_t offset, size_t size,
                                          uint32_t *src);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RET_SRAM_TESTUTILS_H_
