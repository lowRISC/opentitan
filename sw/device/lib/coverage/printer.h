// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COVERAGE_PRINTER_H_
#define OPENTITAN_SW_DEVICE_LIB_COVERAGE_PRINTER_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/* External common runtime APIs */

/**
 * Describes a binary's LLVM single-byte coverage counter buffer and build ID.
 *
 * Exported from `imm_section` as `imm_shared_coverage_profile_desc` under
 * coverage builds so mutable `ROM_EXT` can initialize, report, and invalidate
 * `imm_section` coverage via flash/SRAM data access even after `imm_section`'s
 * ePMP execute window is cleared before owner handoff.
 */
typedef struct coverage_profile_desc {
  const uint8_t *build_id;
  uint8_t *cnts_start;
  uint8_t *cnts_end;
  uint32_t *status;
} coverage_profile_desc_t;

#ifdef OT_PLATFORM_RV32
// `coverage_profile_desc_t` is shared across separately linked binaries
// (`imm_section` and mutable `ROM_EXT`), so lock down its RV32 ABI layout.
OT_ASSERT_MEMBER_OFFSET(coverage_profile_desc_t, build_id, 0);
OT_ASSERT_MEMBER_OFFSET(coverage_profile_desc_t, cnts_start, 4);
OT_ASSERT_MEMBER_OFFSET(coverage_profile_desc_t, cnts_end, 8);
OT_ASSERT_MEMBER_OFFSET(coverage_profile_desc_t, status, 12);
OT_ASSERT_SIZE(coverage_profile_desc_t, 16);
#endif

extern const coverage_profile_desc_t coverage_profile_desc;
extern const coverage_profile_desc_t imm_shared_coverage_profile_desc;

/**
 * @brief Returns whether `desc` describes a populated coverage profile.
 *
 * Weak fallback descriptors (e.g., when no `imm_section` exports coverage
 * state) are zero-initialized with `status == NULL`.
 *
 * @param desc Coverage profile descriptor.
 * @return true if `desc` is non-NULL and has a non-NULL status pointer.
 */
static inline bool coverage_desc_is_present(
    const coverage_profile_desc_t *desc) {
  return desc != NULL && desc->status != NULL;
}

/**
 * @brief Checks if the coverage report described by `desc` is valid.
 *
 * @param desc Coverage profile descriptor.
 * @return true if the report is valid.
 */
bool coverage_is_valid_desc(const coverage_profile_desc_t *desc);

/**
 * @brief Checks if the coverage report described by `desc` has any hit regions.
 *
 * @param desc Coverage profile descriptor.
 * @return true if at least one counter byte is marked covered (`0x00`).
 */
bool coverage_has_hits_desc(const coverage_profile_desc_t *desc);

/**
 * @brief Constructs and sends the profile report described by `desc`.
 *
 * @param desc Coverage profile descriptor.
 */
void coverage_printer_run_desc(const coverage_profile_desc_t *desc);

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
