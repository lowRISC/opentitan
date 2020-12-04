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

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Hardware instantiation parameters for Always-On Timer.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_aon_timer_params {
  /**
   * The base address for the Always-On Timer hardware registers.
   */
  mmio_region_t base_addr;
} dif_aon_timer_params_t;

/**
 * A handle to Always-On Timer.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_aon_timer {
  dif_aon_timer_params_t params;
} dif_aon_timer_t;

/**
 * The result of a Always-On Timer operation.
 */
typedef enum dif_aon_timer_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAonTimerOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifAonTimerError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAonTimerBadArg = 2,
} dif_aon_timer_result_t;

/**
 * The result of a Always-On Timer (watchdog timer) operation.
 */
typedef enum dif_aon_timer_watchdog_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAonTimerWatchdogOk = kDifAonTimerOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAonTimerWatchdogError = kDifAonTimerError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAonTimerWatchdogBadArg = kDifAonTimerBadArg,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  kDifAonTimerWatchdogLocked = 3,
} dif_aon_timer_watchdog_result_t;

/**
 * An Always-On Timer interrupt request type.
 */
typedef enum dif_aon_timer_irq {
  /**
   * Wake-up timer has expired.
   */
  kDifAonTimerIrqWakeupThreshold = 0,
  /**
   * Watchdog timer "Bark" threshold has expired.
   */
  kDifAonTimerIrqWatchdogBarkThreshold,
} dif_aon_timer_irq_t;

/**
 * Creates a new handle for Always-On Timer.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] aon Out param for the initialised handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_init(dif_aon_timer_params_t params,
                                          dif_aon_timer_t *aon);

/** Starts Always-On Timer (wake-up timer).
 *
 * @param aon An Always-On Timer handle.
 * @param threshold Threshold in ticks.
 * @param prescaler 12 bit pre-scaler to enable very long timeouts (one tick
 *                  every N + 1 clock cycles, where N is the pre-scaler value).
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_wakeup_start(const dif_aon_timer_t *aon,
                                                  uint32_t threshold,
                                                  uint32_t prescaler);

/** Stops Always-On Timer (wake-up timer).
 *
 * Stops the timer. Configuration is not touched, and can be restarted via
 * `dif_aon_timer_wakeup_restart`.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_wakeup_stop(const dif_aon_timer_t *aon);

/** Restarts Always-On Timer (wake-up timer).
 *
 * Clears the counter and restarts the timer using the existing configuration.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_wakeup_restart(const dif_aon_timer_t *aon);

/** Retrieves Always-On Timer (wake-up timer) tick count.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] count Current timer tick count.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_wakeup_get_count(
    const dif_aon_timer_t *aon, uint32_t *count);

/** Starts Always-On Timer (watchdog timer).
 *
 * @param aon An Always-On Timer handle.
 * @param bark_threshold "Bark" threshold in ticks.
 * @param bite_threshold "Bite" threshold in ticks.
 * @param pause_in_sleep Watchdog is paused when device is in one of the low
 *        power modes.
 * @param lock Lock access to watchdog configuration registers.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_start(
    const dif_aon_timer_t *aon, uint32_t bark_threshold,
    uint32_t bite_threshold, bool pause_in_sleep, bool lock);

/** Stops Always-On Timer (watchdog timer).
 *
 * Stops the timer. Configuration is not touched, and can be restarted via
 * `dif_aon_timer_watchdog_restart`.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_stop(
    const dif_aon_timer_t *aon);

/** Restarts Always-On Timer (watchdog timer).
 *
 * Clears the counter and restarts the timer using the existing configuration.
 *
 * @param aon An Always-On Timer handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_restart(
    const dif_aon_timer_t *aon);

/** Retrieves Always-On Timer (watchdog timer) tick count.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] count Current timer tick count.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_watchdog_get_count(
    const dif_aon_timer_t *aon, uint32_t *count);

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
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_watchdog_pet(const dif_aon_timer_t *aon);

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
DIF_WARN_UNUSED_RESULT
dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_lock(
    const dif_aon_timer_t *aon);

/**
 * Checks whether this Always-On Timer (watchdog timer) is locked.
 *
 * @param aon An Always-On Timer handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_watchdog_result_t dif_aon_timer_watchdog_is_locked(
    const dif_aon_timer_t *aon, bool *is_locked);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param aon An Always-On Timer handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_irq_is_pending(const dif_aon_timer_t *aon,
                                                    dif_aon_timer_irq_t irq,
                                                    bool *is_pending);

/**
 * Acknowledges a particular interrupt.
 *
 * This operation indicates to the hardware that the interrupt has been
 * successfully serviced.
 *
 * @param aon An Always-On Timer handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_irq_acknowledge(const dif_aon_timer_t *aon,
                                                     dif_aon_timer_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param aon An Always-On Timer handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_aon_timer_result_t dif_aon_timer_irq_force(const dif_aon_timer_t *aon,
                                               dif_aon_timer_irq_t irq);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_AON_TIMER_H_
