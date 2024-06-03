// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_DM_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_DM_H_

/**
 * @file
 * @brief <a href="/book/hw/ip/rv_dm/">RV_DM</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_rv_dm_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Late debug enable/disable configuration.
 *
 * RV_DM is gated by the life cycle controller so that it is only usable in
 * `TEST_UNLOCKED`, `DEV` and `RMA` states. In `DEV` life cycle state, this
 * block supports late debug enablement via firmware, which allows the `ROM` or
 * `ROM_EXT` to implement a debug enablement policy. The debug enablement
 * functionality can be activated by calling this function.
 *
 * @param rv_dm A RV_DM handle.
 * @param enable Enable or disable late debug.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_dm_late_debug_configure(const dif_rv_dm_t *rv_dm,
                                            dif_toggle_t enable);

/**
 * Locks the late debug enable/disable configuration.
 *
 * This function locks the late debug enable/disable configuration register.
 * Once locked, the late debug enable/disable configuration cannot be changed
 * until the next reset.
 *
 * @param rv_dm A RV_DM handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_dm_late_debug_lock(const dif_rv_dm_t *rv_dm);

/**
 * Checks whether the late debug enable/disable configuration is locked.
 *
 * @param rv_dm A RV_DM handle.
 * @param[out] is_locked Out-param for whether the configuration is locked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_dm_late_debug_is_locked(const dif_rv_dm_t *rv_dm,
                                            bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_DM_H_
