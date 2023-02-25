// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_KEYMGR_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_KEYMGR_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/keymgr/doc/">KEYMGR</a> Device Interface Functions
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
 * A handle to keymgr.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_keymgr {
  /**
   * The base address for the keymgr hardware registers.
   */
  mmio_region_t base_addr;
} dif_keymgr_t;

/**
 * Creates a new handle for a(n) keymgr peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the keymgr peripheral.
 * @param[out] keymgr Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_init(mmio_region_t base_addr, dif_keymgr_t *keymgr);

/**
 * A keymgr alert type.
 */
typedef enum dif_keymgr_alert {
  /**
   * Alert for key manager operation errors.  These errors could have been
   * caused by software
   */
  kDifKeymgrAlertRecovOperationErr = 0,
  /**
   * Alert for key manager faults.  These errors cannot be caused by software
   */
  kDifKeymgrAlertFatalFaultErr = 1,
} dif_keymgr_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param keymgr A keymgr handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_alert_force(const dif_keymgr_t *keymgr,
                                    dif_keymgr_alert_t alert);

/**
 * A keymgr interrupt request type.
 */
typedef enum dif_keymgr_irq {
  /**
   * Operation complete
   */
  kDifKeymgrIrqOpDone = 0,
} dif_keymgr_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_keymgr_irq_get_state()`
 * and `dif_keymgr_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_keymgr_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param keymgr A keymgr handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_get_type(const dif_keymgr_t *keymgr,
                                     dif_keymgr_irq_t irq,
                                     dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param keymgr A keymgr handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_get_state(
    const dif_keymgr_t *keymgr, dif_keymgr_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param keymgr A keymgr handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_is_pending(const dif_keymgr_t *keymgr,
                                       dif_keymgr_irq_t irq, bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param keymgr A keymgr handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_acknowledge_state(
    const dif_keymgr_t *keymgr, dif_keymgr_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param keymgr A keymgr handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_acknowledge_all(const dif_keymgr_t *keymgr);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param keymgr A keymgr handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_acknowledge(const dif_keymgr_t *keymgr,
                                        dif_keymgr_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param keymgr A keymgr handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_force(const dif_keymgr_t *keymgr,
                                  dif_keymgr_irq_t irq, const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_keymgr_irq_disable_all()` and `dif_keymgr_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_keymgr_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param keymgr A keymgr handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_get_enabled(const dif_keymgr_t *keymgr,
                                        dif_keymgr_irq_t irq,
                                        dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param keymgr A keymgr handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_set_enabled(const dif_keymgr_t *keymgr,
                                        dif_keymgr_irq_t irq,
                                        dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param keymgr A keymgr handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_disable_all(
    const dif_keymgr_t *keymgr, dif_keymgr_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param keymgr A keymgr handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_keymgr_irq_restore_all(
    const dif_keymgr_t *keymgr,
    const dif_keymgr_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_KEYMGR_AUTOGEN_H_
