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
 * expectations and trigger an exception on fault detection.
 *
 * Initialization
 *
 * - `sec_mmio_init()`.
 *
 * Register writes
 *
 * - Perform a number (N) of calls to `sec_mmio_write32()`.
 * - Increment the expected number of writes by N with
 *   `SEC_MMIO_WRITE_INCREMENT()`. This is done using a separate function call
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
 */

enum {
  /**
   * Number of registers stored in the sec_mmio context.
   */
  kSecMmioRegFileSize = 1000,
};

/**
 * Working context.
 *
 * Contains list of expected register addresses and associated values, as well
 * as expected counters.
 */
typedef struct sec_mmio_ctx {
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
   * `SEC_MMIO_WRITE_INCREMENT()`.
   */
  uint32_t expected_write_count;
  /**
   * Represents the number of times the check functions have been called.
   * Incremented by the `sec_mmio_check_values()` and the
   * `sec_mmio_check_counters()` functions.
   */
  uint32_t check_count;
  /**
   * List of expected register values.
   */
  uint32_t values[kSecMmioRegFileSize];
  /**
   * List of expected register addresses.
   */
  uint32_t addrs[kSecMmioRegFileSize];
} sec_mmio_ctx_t;

/**
 * The `sec_mmio_ctx_t` structure is accessible by both the ROM and ROM
 * extension. It's layout is therefore fixed and any changes must be applied
 * to both boot stages.
 */
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, last_index, 0);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, write_count, 4);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, expected_write_count, 8);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, check_count, 12);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, values, 16);
OT_ASSERT_MEMBER_OFFSET(sec_mmio_ctx_t, addrs, 4016);
OT_ASSERT_SIZE(sec_mmio_ctx_t, 8016);  // Checked by linker script.

// The sec_mmio_ctx is referenced here to be able to use it inside the
// `SEC_MMIO_WRITE_INCREMENT()` macro.
extern sec_mmio_ctx_t sec_mmio_ctx;

/**
 * Increment the expected count of register writes by `value`.
 *
 * This macro must be used to increment the number of expected register writes
 * before calling `sec_mmio_check_counters()`.
 *
 * @param value The expected write count increment.
 */
#define SEC_MMIO_WRITE_INCREMENT(value) \
  (sec_mmio_ctx.expected_write_count += (value))

/**
 * Assert macro used to cross-reference exported sec_mmio expected write counts
 * to their respective functions.
 */
#define SEC_MMIO_ASSERT_WRITE_INCREMENT(enum_val, expected) \
  static_assert(enum_val == expected, "Unexpected value for " #enum_val)

/**
 * Initializes the module.
 *
 * Initializes the internal `sec_mmio_ctx_t` context.
 */
void sec_mmio_init(void);

/**
 * Executes sec_mmio next boot stage initialization.
 *
 * Performs the following operations to the internal `sec_mmio_ctx_t` context:
 *
 * - Clear the check count. This allows the caller to reset the
 *   `sec_mmio_check_counters()` expected count argument.
 * - Reset all expected address and values in the expectations table starting at
 *   the last_index.
 */
void sec_mmio_next_stage_init(void);

/**
 * Reads an aligned uint32_t from the MMIO region `addr`.
 *
 * This function implements a read-read-comparison operation. The first read
 * is stored in the list of expected register values for later comparison
 * via `sec_mmio_check_values()`.
 *
 * An exception is thrown if the comparison operation fails.
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
 * writes. The caller is responsible to setting the expected write count with
 * `SEC_MMIO_WRITE_INCREMENT()`.
 *
 * An exception is thrown if the comparison operation fails.
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
 * writes. The caller is responsible to setting the expected write count with
 * `SEC_MMIO_WRITE_INCREMENT()`.
 *
 * An exception is thrown if the comparison operation fails.
 *
 * @param addr The address to write to.
 * @param value The value to write.
 */
void sec_mmio_write32_shadowed(uint32_t addr, uint32_t value);

/**
 * Checks the expected list of register values.
 *
 * All expected register values are verified against expectations. An exception
 * is thrown if any of the comparison fails.
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
 * Checks the expected number of register writes and check counts. An exception
 * is thrown if the counters fail to match expectations.
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
