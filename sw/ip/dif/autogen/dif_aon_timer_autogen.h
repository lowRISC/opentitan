// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_AON_TIMER_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_AON_TIMER_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/aon_timer/doc/">AON_TIMER</a> Device Interface
 * Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to aon_timer.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_aon_timer {
  /**
   * The base address for the aon_timer hardware registers.
   */
  mmio_region_t base_addr;
} dif_aon_timer_t;

/**
 * Creates a new handle for a(n) aon_timer peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the aon_timer peripheral.
 * @param[out] aon_timer Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_init(mmio_region_t base_addr,
                                dif_aon_timer_t *aon_timer);

/**
 * A aon_timer alert type.
 */
typedef enum dif_aon_timer_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifAonTimerAlertFatalFault = 0,
} dif_aon_timer_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param aon_timer A aon_timer handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_alert_force(const dif_aon_timer_t *aon_timer,
                                       dif_aon_timer_alert_t alert);

/**
 * A aon_timer interrupt request type.
 */
typedef enum dif_aon_timer_irq {
  /**
   * Raised if the wakeup timer has hit the specified threshold
   */
  kDifAonTimerIrqWkupTimerExpired = 0,
  /**
   * Raised if the watchdog timer has hit the bark threshold
   */
  kDifAonTimerIrqWdogTimerBark = 1,
} dif_aon_timer_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_aon_timer_irq_get_state()`
 * and `dif_aon_timer_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_aon_timer_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param aon_timer A aon_timer handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_get_type(const dif_aon_timer_t *aon_timer,
                                        dif_aon_timer_irq_t irq,
                                        dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param aon_timer A aon_timer handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_get_state(
    const dif_aon_timer_t *aon_timer,
    dif_aon_timer_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param aon_timer A aon_timer handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_is_pending(const dif_aon_timer_t *aon_timer,
                                          dif_aon_timer_irq_t irq,
                                          bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param aon_timer A aon_timer handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_acknowledge_state(
    const dif_aon_timer_t *aon_timer,
    dif_aon_timer_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param aon_timer A aon_timer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_acknowledge_all(
    const dif_aon_timer_t *aon_timer);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param aon_timer A aon_timer handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_acknowledge(const dif_aon_timer_t *aon_timer,
                                           dif_aon_timer_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param aon_timer A aon_timer handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aon_timer_irq_force(const dif_aon_timer_t *aon_timer,
                                     dif_aon_timer_irq_t irq, const bool val);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_AON_TIMER_AUTOGEN_H_
