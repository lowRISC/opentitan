// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_EDN_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_EDN_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/edn/doc/">EDN</a> Device Interface Functions
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
 * A handle to edn.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_edn {
  /**
   * The base address for the edn hardware registers.
   */
  mmio_region_t base_addr;
} dif_edn_t;

/**
 * Creates a new handle for a(n) edn peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the edn peripheral.
 * @param[out] edn Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_init(mmio_region_t base_addr, dif_edn_t *edn);

/**
 * A edn alert type.
 */
typedef enum dif_edn_alert {
  /**
   * This alert is triggered when entropy bus data matches on consecutive clock
   * cycles.
   */
  kDifEdnAlertRecovAlert = 0,
  /**
   * This alert triggers (i) if an illegal state machine state is reached, or
   * (ii) if a fatal integrity failure is detected on the TL-UL bus.
   */
  kDifEdnAlertFatalAlert = 1,
} dif_edn_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param edn A edn handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_alert_force(const dif_edn_t *edn, dif_edn_alert_t alert);

/**
 * A edn interrupt request type.
 */
typedef enum dif_edn_irq {
  /**
   * Asserted when a software CSRNG request has completed.
   */
  kDifEdnIrqEdnCmdReqDone = 0,
  /**
   * Asserted when a FIFO error occurs.
   */
  kDifEdnIrqEdnFatalErr = 1,
} dif_edn_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_edn_irq_get_state()`
 * and `dif_edn_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_edn_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param edn A edn handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_type(const dif_edn_t *edn, dif_edn_irq_t irq,
                                  dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param edn A edn handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_state(const dif_edn_t *edn,
                                   dif_edn_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param edn A edn handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_is_pending(const dif_edn_t *edn, dif_edn_irq_t irq,
                                    bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param edn A edn handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_acknowledge_state(
    const dif_edn_t *edn, dif_edn_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param edn A edn handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_acknowledge_all(const dif_edn_t *edn);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param edn A edn handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_acknowledge(const dif_edn_t *edn, dif_edn_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param edn A edn handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_force(const dif_edn_t *edn, dif_edn_irq_t irq,
                               const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_edn_irq_disable_all()` and `dif_edn_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_edn_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param edn A edn handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_get_enabled(const dif_edn_t *edn, dif_edn_irq_t irq,
                                     dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param edn A edn handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_set_enabled(const dif_edn_t *edn, dif_edn_irq_t irq,
                                     dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param edn A edn handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_disable_all(const dif_edn_t *edn,
                                     dif_edn_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param edn A edn handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_irq_restore_all(
    const dif_edn_t *edn, const dif_edn_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_EDN_AUTOGEN_H_
