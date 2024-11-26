// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_ALERT_HANDLER_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_ALERT_HANDLER_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/book/hw/ip/alert_handler/">ALERT_HANDLER</a> Device
 * Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "dt_alert_handler.h"  // Generated.
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to alert_handler.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_alert_handler {
  /**
   * The base address for the alert_handler hardware registers.
   */
  mmio_region_t base_addr;
} dif_alert_handler_t;

/**
 * Creates a new handle for a(n) alert_handler peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the alert_handler peripheral.
 * @param[out] alert_handler Out param for the initialized handle.
 * @return The result of the operation.
 *
 * DEPRECATED This function exists solely for the transition to
 * dt-based DIFs and will be removed in the future.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_init(mmio_region_t base_addr,
                                    dif_alert_handler_t *alert_handler);

/**
 * Creates a new handle for a(n) alert_handler peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param dt The devicetable description of the device.
 * @param[out] alert_handler Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_init_from_dt(const dt_alert_handler_t *dt,
                                            dif_alert_handler_t *alert_handler);

/**
 * A alert_handler interrupt request type.
 *
 * DEPRECATED Use `dt_alert_handler_irq_t` instead.
 * This enumeration exists solely for the transition to
 * dt-based interrupt numbers and will be removed in the future.
 *
 * The following are defines to keep the types consistent with DT.
 */
/**
 * Interrupt state bit of Class A. Set by HW in case an alert within this class
 * triggered. Defaults true, write one to clear.
 */
#define kDifAlertHandlerIrqClassa kDtAlertHandlerIrqClassa
/**
 * Interrupt state bit of Class B. Set by HW in case an alert within this class
 * triggered. Defaults true, write one to clear.
 */
#define kDifAlertHandlerIrqClassb kDtAlertHandlerIrqClassb
/**
 * Interrupt state bit of Class C. Set by HW in case an alert within this class
 * triggered. Defaults true, write one to clear.
 */
#define kDifAlertHandlerIrqClassc kDtAlertHandlerIrqClassc
/**
 * Interrupt state bit of Class D. Set by HW in case an alert within this class
 * triggered. Defaults true, write one to clear.
 */
#define kDifAlertHandlerIrqClassd kDtAlertHandlerIrqClassd

// DEPRECATED This typedef exists solely for the transition to
// dt-based interrupt numbers and will be removed in the future.
typedef dt_alert_handler_irq_t dif_alert_handler_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_alert_handler_irq_get_state()` and
 * `dif_alert_handler_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_alert_handler_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param alert_handler A alert_handler handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_get_type(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_irq_t,
    dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param alert_handler A alert_handler handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_get_state(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param alert_handler A alert_handler handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_is_pending(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_irq_t,
    bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param alert_handler A alert_handler handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_acknowledge_state(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param alert_handler A alert_handler handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_acknowledge_all(
    const dif_alert_handler_t *alert_handler);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param alert_handler A alert_handler handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_acknowledge(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_irq_t);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param alert_handler A alert_handler handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_force(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_irq_t,
    const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_alert_handler_irq_disable_all()` and
 * `dif_alert_handler_irq_restore_all()` functions.
 */
typedef uint32_t dif_alert_handler_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param alert_handler A alert_handler handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_get_enabled(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_irq_t,
    dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param alert_handler A alert_handler handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_set_enabled(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_irq_t,
    dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param alert_handler A alert_handler handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_disable_all(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param alert_handler A alert_handler handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_irq_restore_all(
    const dif_alert_handler_t *alert_handler,
    const dif_alert_handler_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_ALERT_HANDLER_AUTOGEN_H_
