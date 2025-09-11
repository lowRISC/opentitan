// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COVERAGE_PRINTER_H_
#define OPENTITAN_SW_DEVICE_LIB_COVERAGE_PRINTER_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/* External common runtime APIs */

/**
 * @brief Checks if the current coverage report is valid.
 *
 * A report can be invalidated if the device resets or if
 * `coverage_invalidate()` is explicitly called.
 *
 * @return true if the report is valid.
 */
bool coverage_is_valid(void);

/**
 * @brief Invalidates the current coverage report.
 *
 * This function sets an internal status flag to mark the current coverage data
 * as invalid, typically used to indicate a failed test or an unexpected reset.
 */
void coverage_invalidate(void);

/**
 * @brief Initializes the coverage data.
 *
 * This function initializes the LLVM coverage counters to a uncovered (0xFF)
 * and sets up the initial validity status for the coverage report.
 */
void coverage_init(void);

/* Internal APIs for actual runtime */

/**
 * @brief Console sink provided by the actual runtime.
 *
 * This function is an external dependency that must be implemented by the
 * specific runtime environment (e.g., UART, OTTF) to output the raw coverage
 * data.
 *
 * @param data Pointer to the data buffer to be sent.
 * @param size The number of bytes to send.
 */
extern void coverage_printer_sink(const void *data, size_t size);

/**
 * @brief Constructs the profile report and sends it via
 * `coverage_printer_sink`.
 *
 * This function gathers the LLVM coverage counter data, compresses it,
 * calculates a CRC, and sends the final report through the
 * `coverage_printer_sink`.
 */
void coverage_printer_run(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_COVERAGE_PRINTER_H_
