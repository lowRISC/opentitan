// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AON_TIMER_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AON_TIMER_H_

/**
 * @file
 * @brief <a href="/hw/ip/aon_timer/doc/">Always-On Timer</a> Device Interface
 * Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_aon_timer_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Starts Always-On Timer (wake-up timer).
 *
 * This operation starts the wake-up timer with the provided configuration.
 * Note that the timer is stopped and counter cleared, before the timer is
 * started with the new configuration.
 *
 * @param aon An Always-On Timer handle.
 * @param threshold Threshold in ticks.
 * @param prescaler 12 bit pre-scaler to enable very long timeouts (one tick
 *                  every N + 1 clock cycles, where N is the pre-scaler value).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_wakeup_start(const dif_aon_timer_t *aon,
                                        uint32_t threshold, uint32_t prescaler);

/** Stops Always-On Timer (wake-up timer).
 *
 * Stops the timer. Configuration is not touched, and can be restarted via
 * `dif_aon_timer_wakeup_restart`.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_wakeup_stop(const dif_aon_timer_t *aon);

/** Restarts Always-On Timer (wake-up timer).
 *
 * Clears the counter and restarts the timer using the existing configuration.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_wakeup_restart(const dif_aon_timer_t *aon);

/**
 * Checks whether this Always-On Timer (wake-up timer) is enabled.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] is_enabled Out-param for the enabled state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_wakeup_is_enabled(const dif_aon_timer_t *aon,
                                             bool *is_enabled);

/** Clear Always-On Timer wakeup cause
 *
 * Clears WKUP_CAUSE register
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_clear_wakeup_cause(const dif_aon_timer_t *aon);

/** Retrieves Always-On Timer (wake-up timer) tick count.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] count Current timer tick count.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_wakeup_get_count(const dif_aon_timer_t *aon,
                                            uint32_t *count);

/** Starts Always-On Timer (watchdog timer).
 *
 * This operation starts the watchdog timer with the provided configuration.
 * Note that the timer is stopped and counter cleared, before the timer is
 * started with the new configuration.
 *
 * @param aon An Always-On Timer handle.
 * @param bark_threshold "Bark" threshold in ticks.
 * @param bite_threshold "Bite" threshold in ticks.
 * @param pause_in_sleep Watchdog is paused when device is in one of the low
 *        power modes.
 * @param lock Lock access to watchdog configuration registers.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_start(const dif_aon_timer_t *aon,
                                          uint32_t bark_threshold,
                                          uint32_t bite_threshold,
                                          bool pause_in_sleep, bool lock);

/** Stops Always-On Timer (watchdog timer).
 *
 * Stops the timer. Configuration is not touched, and can be restarted via
 * `dif_aon_timer_watchdog_restart`.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_stop(const dif_aon_timer_t *aon);

/** Restarts Always-On Timer (watchdog timer).
 *
 * Clears the counter and restarts the timer using the existing configuration.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_restart(const dif_aon_timer_t *aon);

/**
 * Checks whether this Always-On Timer (watchdog timer) is enabled.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] is_enabled Out-param for the enabled state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_is_enabled(const dif_aon_timer_t *aon,
                                               bool *is_enabled);

/** Retrieves Always-On Timer (watchdog timer) tick count.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] count Current timer tick count.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_get_count(const dif_aon_timer_t *aon,
                                              uint32_t *count);

/** Clears Always-On Timer (watchdog timer).
 *
 * This function must be called periodically to satisfy "Bite" and "Bark"
 * thresholds. The semantics of this function are similar to
 * `dif_aon_timer_watchdog_restart`, however it does not write to the control
 * register, and is guaranteed to succeed even when the watchdog is locked.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_pet(const dif_aon_timer_t *aon);

/**
 * Locks Always-On Timer (watchdog timer).
 *
 * The watchdog configuration will be locked until the next reset. This means
 * that this timer cannot be stopped, restarted or reconfigured, however the
 * count can be cleared via `dif_aon_timer_watchdog_pet`.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_lock(const dif_aon_timer_t *aon);

/**
 * Checks whether this Always-On Timer (watchdog timer) is locked.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_watchdog_is_locked(const dif_aon_timer_t *aon,
                                              bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AON_TIMER_H_
