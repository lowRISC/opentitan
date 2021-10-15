// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_SEC_MMIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_SEC_MMIO_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file
 * @brief Secure Memory-mapped IO functions, for volatile access.
 *
 * This module is responsible for tracking critical register values for an
 * initialized context `sec_mmio_ctx_t`, and provides a mechanism to evaluate
 * expectations and trigger shutdown escalation on fault detection.
 *
 * Initialization
 *
 * - `sec_mmio_init()`.
 *
 * Register writes
 *
 * - Perform a number (N) of calls to `sec_mmio_write32()`.
 * - Increment the expected number of writes by N by calling
 *   `sec_mmio_write_increment()`. This is done using a separate function call
 *   to be able to detect skip instruciton faults on `sec_mmio_write32()`
 *   calls.
 *
 * Register reads
 *
 * Use the `sec_mmio_read32()`.
 *
 * Expectation checks
 *
 * See the following:
 *
 * - `sec_mmio_check_values()`
 * - `sec_mmio_check_counters()`
 *
 * Opens:
 *
 * - Currently fault detection escalations are performed by calling a handler
 *   that is registered at `sec_mmio_init()` call time. Need to determine if we
 *   want to move to a mock_shutdown implementation, or if we want to refactor
 *   the code to return error codes.
 */

enum {
  /**
   * Number of registers stored in the sec_mmio context.
   *
   * This value must be less than the `kSecMmioRndStep` in sec_mmio.c.
   */
  // TODO(#6609): Update size of expectations table.
  kSecMmioRegFileSize = 200,
};

/**
 * Working context.
 *
 * Contains list of expected register addresses and associated values, as well
 * as expected counters.
 */
typedef struct sec_mmio_ctx {
  /**
   * List of expected register values.
   */
  uint32_t values[kSecMmioRegFileSize];

  /**
   * List of expected register addresses.
   */
  uint32_t addrs[kSecMmioRegFileSize];

  /**
   * Represents the expected number of register values.
   */
  uint32_t last_index;
  /**
   * Represents the number of register write operations. Incremented by the
   * `sec_mmio_write32()` function.
   */
  uint32_t write_count;
  /**
   * Represents the expected number of register write operations. Incremented by
   * the `sec_mmio_write_increment()` function.
   */
  uint32_t expected_write_count;
  /**
   * Represents the number of times the check functions have been called.
   * Incremented by the `sec_mmio_check_values()` and the
   * `sec_mmio_check_counters()` functions.
   */
  uint32_t check_count;
} sec_mmio_ctx_t;

/**
 * The `sec_mmio_ctx_t` structure is accessible by both the mask ROM and ROM
 * extension. It's layout is therefore fixed and any changes must be applied
 * to both boot stages.
 */
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, values, 0);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, addrs, 800);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, last_index, 1600);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, write_count, 1604);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, expected_write_count, 1608);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, check_count, 1612);
OT_ASSERT_SIZE(sec_mmio_ctx_t, 1616);  // Checked by linker script.

/**
 * Shutdown module callback handler.
 */
typedef void (*sec_mmio_shutdown_handler)(rom_error_t);

/**
 * Initializes the module.
 *
 * Registers the `cb` callback handler and initializes the internal
 * `sec_mmio_ctx_t` context.
 *
 * @param cb Shutdown module callback handler.
 */
void sec_mmio_init(sec_mmio_shutdown_handler cb);

/**
 * Executes sec_mmio next boot stage initialization.
 *
 * Registers the `cb` callback handler, and performs the following operations to
 * the internal `sec_mmio_ctx_t` context:
 *
 * - Clear the check count. This allows the caller to reset the
 *   `sec_mmio_check_counters()` expected count argument.
 * - Reset all expected address and values in the expectations table starting at
 *   the last_index.
 *
 * @param cb Shutdown module callback handler.
 */
void sec_mmio_next_stage_init(sec_mmio_shutdown_handler cb);

/**
 * Reads an aligned uint32_t from the MMIO region `addr`.
 *
 * This function implements a read-read-comparison operation. The first read
 * is stored in the list of expected register values for later comparison
 * via `sec_mmio_check_values()`.
 *
 * A shutdown sequence is initiated if the comparison operation fails.
 *
 * @param addr The address to read from.
 * @return the read value.
 */
uint32_t sec_mmio_read32(uint32_t addr);

/**
 * Writes an aligned uint32_t to the MMIO region `base` at the give byte
 * `offset`.
 *
 * This function implements a write-read-comparison operation. The first write
 * value is stored in the list of expected register values for later comparison
 * via `sec_mmio_check_values()`.
 *
 * On successful calls, this function will increment the internal count of
 * writes. The caller is responsible to setting the expected write count by
 * calling `sec_mmio_write_increment()`.
 *
 * A shutdown sequence is initiated if the comparison operation fails.
 *
 * @param addr The address to write to.
 * @param value The value to write.
 */
void sec_mmio_write32(uint32_t addr, uint32_t value);

/**
 * Writes an aligned uint32_t to the MMIO region `base` at the give byte
 * `offset`.
 *
 * This function implements a write-write-read-comparison operation for shadowed
 * registers. The first write value is stored in the list of expected register
 * values for later comparison via `sec_mmio_check_values()`.
 *
 * On successful calls, this function will increment the internal count of
 * writes. The caller is responsible to setting the expected write count by
 * calling `sec_mmio_write_increment()`.
 *
 * A shutdown sequence is initiated if the comparison operation fails.
 *
 * @param addr The address to write to.
 * @param value The value to write.
 */
void sec_mmio_write32_shadowed(uint32_t addr, uint32_t value);

/**
 * Increment the expected count of register writes by `value`.
 *
 * @param value The expected write count increment.
 */
void sec_mmio_write_increment(uint32_t value);

/**
 * Checks the expected list of register values.
 *
 * All expected register values are verified against expectations. A shutdown
 * sequence is initiated if any of the comparison fails.
 *
 * The `rnd_offset` parameter can be set to a random value to randomize the
 * order of reads.
 *
 * Calling this function will increment the check function counter on a
 * successful call.
 *
 * The `rnd_offset` parameter can be generated by calling the entropy source or
 * the CSRNG driver.
 *
 * @param rnd_offset A random value used to generate a random read sequence.
 */
void sec_mmio_check_values(uint32_t rnd_offset);

/**
 * Checks the expected counter state.
 *
 * Checks the expected number of register writes and check counts. A shutdown
 * sequence is initiated if the counters fail to match expectations.
 *
 * Calling this function will increment the check function counter on a
 * successful
 *
 * @param expected_check_count The expected check counter.
 */
void sec_mmio_check_counters(uint32_t expected_check_count);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_SEC_MMIO_H_
