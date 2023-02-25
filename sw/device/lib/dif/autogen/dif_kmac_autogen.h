// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_KMAC_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_KMAC_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/kmac/doc/">KMAC</a> Device Interface Functions
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
 * A handle to kmac.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_kmac {
  /**
   * The base address for the kmac hardware registers.
   */
  mmio_region_t base_addr;
} dif_kmac_t;

/**
 * Creates a new handle for a(n) kmac peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the kmac peripheral.
 * @param[out] kmac Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_init(mmio_region_t base_addr, dif_kmac_t *kmac);

/**
 * A kmac alert type.
 */
typedef enum dif_kmac_alert {
  /**
   * Alert for KMAC operation error. It occurs when the shadow registers have
   * update errors.
   */
  kDifKmacAlertRecovOperationErr = 0,
  /**
   * This fatal alert is triggered when a fatal error is detected inside the
   * KMAC unit. Examples for such faults include: i) TL-UL bus integrity fault.
   * ii) Storage errors in the shadow registers. iii) Errors in the message,
   * round, or key counter. iv) Any internal FSM entering an invalid state. v)
   * An error in the redundant lfsr. The KMAC unit cannot recover from such an
   * error and needs to be reset.
   */
  kDifKmacAlertFatalFaultErr = 1,
} dif_kmac_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param kmac A kmac handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_alert_force(const dif_kmac_t *kmac,
                                  dif_kmac_alert_t alert);

/**
 * A kmac interrupt request type.
 */
typedef enum dif_kmac_irq {
  /**
   * KMAC/SHA3 absorbing has been completed
   */
  kDifKmacIrqKmacDone = 0,
  /**
   * Message FIFO empty condition
   */
  kDifKmacIrqFifoEmpty = 1,
  /**
   * KMAC/SHA3 error occurred. ERR_CODE register shows the details
   */
  kDifKmacIrqKmacErr = 2,
} dif_kmac_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_kmac_irq_get_state()`
 * and `dif_kmac_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_kmac_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param kmac A kmac handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_get_type(const dif_kmac_t *kmac, dif_kmac_irq_t irq,
                                   dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param kmac A kmac handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_get_state(const dif_kmac_t *kmac,
                                    dif_kmac_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param kmac A kmac handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_is_pending(const dif_kmac_t *kmac, dif_kmac_irq_t irq,
                                     bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param kmac A kmac handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_acknowledge_state(
    const dif_kmac_t *kmac, dif_kmac_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param kmac A kmac handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_acknowledge_all(const dif_kmac_t *kmac);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param kmac A kmac handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_acknowledge(const dif_kmac_t *kmac,
                                      dif_kmac_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param kmac A kmac handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_force(const dif_kmac_t *kmac, dif_kmac_irq_t irq,
                                const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_kmac_irq_disable_all()` and `dif_kmac_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_kmac_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param kmac A kmac handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_get_enabled(const dif_kmac_t *kmac,
                                      dif_kmac_irq_t irq, dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param kmac A kmac handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_set_enabled(const dif_kmac_t *kmac,
                                      dif_kmac_irq_t irq, dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param kmac A kmac handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_disable_all(const dif_kmac_t *kmac,
                                      dif_kmac_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param kmac A kmac handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_kmac_irq_restore_all(
    const dif_kmac_t *kmac, const dif_kmac_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_KMAC_AUTOGEN_H_
