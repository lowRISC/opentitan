// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_DMA_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_DMA_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/book/hw/ip/dma/">DMA</a> Device Interface Functions
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
 * A handle to dma.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_dma {
  /**
   * The base address for the dma hardware registers.
   */
  mmio_region_t base_addr;
} dif_dma_t;

/**
 * Creates a new handle for a(n) dma peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the dma peripheral.
 * @param[out] dma Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_init(mmio_region_t base_addr, dif_dma_t *dma);

/**
 * A dma alert type.
 */
typedef enum dif_dma_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifDmaAlertFatalFault = 0,
} dif_dma_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param dma A dma handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_alert_force(const dif_dma_t *dma, dif_dma_alert_t alert);

/**
 * A dma interrupt request type.
 */
typedef enum dif_dma_irq {
  /**
   * DMA operation has been completed.
   */
  kDifDmaIrqDmaDone = 0,
  /**
   * DMA error has occurred. DMA_STATUS.error_code register shows the details.
   */
  kDifDmaIrqDmaError = 1,
} dif_dma_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_dma_irq_get_state()`
 * and `dif_dma_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_dma_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param dma A dma handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_get_type(const dif_dma_t *dma, dif_dma_irq_t irq,
                                  dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param dma A dma handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_get_state(const dif_dma_t *dma,
                                   dif_dma_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param dma A dma handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_is_pending(const dif_dma_t *dma, dif_dma_irq_t irq,
                                    bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param dma A dma handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_acknowledge_state(
    const dif_dma_t *dma, dif_dma_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param dma A dma handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_acknowledge_all(const dif_dma_t *dma);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param dma A dma handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_acknowledge(const dif_dma_t *dma, dif_dma_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param dma A dma handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_force(const dif_dma_t *dma, dif_dma_irq_t irq,
                               const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_dma_irq_disable_all()` and `dif_dma_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_dma_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param dma A dma handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_get_enabled(const dif_dma_t *dma, dif_dma_irq_t irq,
                                     dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param dma A dma handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_set_enabled(const dif_dma_t *dma, dif_dma_irq_t irq,
                                     dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param dma A dma handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_disable_all(const dif_dma_t *dma,
                                     dif_dma_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param dma A dma handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_restore_all(
    const dif_dma_t *dma, const dif_dma_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_DMA_AUTOGEN_H_
