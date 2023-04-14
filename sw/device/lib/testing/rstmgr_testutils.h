// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RSTMGR_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RSTMGR_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rstmgr.h"

/**
 * Determines if the reset_info matches info.
 *
 * @param rstmgr A reset manager handle.
 * @param info A bit mask of reset reasons.
 * @return `kOk(res)` Where `res` is true if the reset_info CSR matches info or
 * `kInternal` in case of error.
 */
OT_WARN_UNUSED_RESULT
status_t rstmgr_testutils_is_reset_info(const dif_rstmgr_t *rstmgr,
                                        dif_rstmgr_reset_info_bitfield_t info);

/**
 * Determines if the reset info contains any of the reasons in `info`.
 *
 * @param rstmgr A reset manager handle.
 * @param info A bit mask of reset reasons.
 * @return `kOk(res)` Where `res` is true if the reset info contains any of the
 * reasons in `info` or `kInternal` in case of error.
 */
OT_WARN_UNUSED_RESULT
status_t rstmgr_testutils_reset_info_any(const dif_rstmgr_t *rstmgr,
                                         dif_rstmgr_reset_info_bitfield_t info);

/**
 * Compares the given alert dump against the device's.
 *
 * If the dump array is null or its size is zero this check succeeds. It is
 * possible to compare less words than the device captures, but it is an error
 * to try to compare more.
 *
 * @param rstmgr A reset manager handle.
 * @param expected_alert_dump An array holding the expected alert dump.
 * @param dump_size The size of the expected_alert_dump array.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rstmgr_testutils_compare_alert_info(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_alert_info_dump_segment_t *expected_alert_dump,
    size_t dump_size);

/**
 * Compares the given cpu dump against the device's.
 *
 * If the dump array is null or its size is zero this check succeeds. It is
 * possible to compare less words than the device captures, but it is an error
 * to try to compare more.
 *
 * @param rstmgr A reset manager handle.
 * @param expected_cpu_dump An array holding the expected cpu dump.
 * @param dump_size The size of the expected_cpu_dump array.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rstmgr_testutils_compare_cpu_info(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_cpu_info_dump_segment_t *expected_cpu_dump, size_t dump_size);

/**
 * Prepares the rstmgr for a reset scenario.
 *
 * @param rstmgr A reset manager handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rstmgr_testutils_pre_reset(const dif_rstmgr_t *rstmgr);

/**
 * Checks state after a reset.
 *
 * This will cause a failure if any of the checks fail. If either of the dump
 * arrays is null or its size is zero the corresponding comparison will be
 * skipped.
 *
 * @param rstmgr A reset manager handle.
 * @param expected_reset_info The expected contents of the reset_info CSR.
 * @param expected_alert_dump An array with the expected contents of the
 *                            alert_info CSR.
 * @param alert_dump_size The size of the expected_alert_dump array.
 * @param expected_cpu_dump An array with the expected contents of the cpu_info
 *                          CSR.
 * @param cpu_dump_size The size of the expected_cpu_dump array.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rstmgr_testutils_post_reset(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_reset_info_bitfield_t expected_reset_info,
    dif_rstmgr_alert_info_dump_segment_t *expected_alert_dump,
    size_t alert_dump_size,
    dif_rstmgr_cpu_info_dump_segment_t *expected_cpu_dump,
    size_t cpu_dump_size);

/**
 * Gets the reason for a reset in retention SRAM.
 *
 * @returns reset reason
 */
dif_rstmgr_reset_info_bitfield_t rstmgr_testutils_reason_get(void);

/**
 * Clears the reset information in Retention SRAM
 */
void rstmgr_testutils_reason_clear(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RSTMGR_TESTUTILS_H_
