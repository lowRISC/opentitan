// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_UART_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_UART_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/book/hw/ip/uart/">UART</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "dt_uart.h"  // Generated.
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to uart.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_uart {
  /**
   * The base address for the uart hardware registers.
   */
  mmio_region_t base_addr;
} dif_uart_t;

/**
 * Creates a new handle for a(n) uart peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the uart peripheral.
 * @param[out] uart Out param for the initialized handle.
 * @return The result of the operation.
 *
 * DEPRECATED This function exists solely for the transition to
 * dt-based DIFs and will be removed in the future.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_init(mmio_region_t base_addr, dif_uart_t *uart);

/**
 * Creates a new handle for a(n) uart peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param dt The devicetable description of the device.
 * @param[out] uart Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_init_from_dt(const dt_uart_t *dt, dif_uart_t *uart);

/**
 * A uart alert type.
 */
typedef enum dif_uart_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifUartAlertFatalFault = 0,
} dif_uart_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param uart A uart handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_alert_force(const dif_uart_t *uart,
                                  dif_uart_alert_t alert);

/**
 * A uart interrupt request type.
 *
 * DEPRECATED Use `dt_uart_irq_t` instead.
 * This enumeration exists solely for the transition to
 * dt-based interrupt numbers and will be removed in the future.
 *
 * The following are defines to keep the types consistent with DT.
 */
/**
 * Raised if the transmit FIFO is past the high-water mark.
 */
#define kDifUartIrqTxWatermark kDtUartIrqTxWatermark
/**
 * Raised if the receive FIFO is past the high-water mark.
 */
#define kDifUartIrqRxWatermark kDtUartIrqRxWatermark
/**
 * Raised if the transmit FIFO has emptied and no transmit is ongoing.
 */
#define kDifUartIrqTxDone kDtUartIrqTxDone
/**
 * Raised if the receive FIFO has overflowed.
 */
#define kDifUartIrqRxOverflow kDtUartIrqRxOverflow
/**
 * Raised if a framing error has been detected on receive.
 */
#define kDifUartIrqRxFrameErr kDtUartIrqRxFrameErr
/**
 * Raised if break condition has been detected on receive.
 */
#define kDifUartIrqRxBreakErr kDtUartIrqRxBreakErr
/**
 * Raised if RX FIFO has characters remaining in the FIFO without being
 * retrieved for the programmed time period.
 */
#define kDifUartIrqRxTimeout kDtUartIrqRxTimeout
/**
 * Raised if the receiver has detected a parity error.
 */
#define kDifUartIrqRxParityErr kDtUartIrqRxParityErr
/**
 * Raised if the transmit FIFO is empty.
 */
#define kDifUartIrqTxEmpty kDtUartIrqTxEmpty

// DEPRECATED This typedef exists solely for the transition to
// dt-based interrupt numbers and will be removed in the future.
typedef dt_uart_irq_t dif_uart_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_uart_irq_get_state()`
 * and `dif_uart_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_uart_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_get_type(const dif_uart_t *uart, dif_uart_irq_t,
                                   dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param uart A uart handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_get_state(const dif_uart_t *uart,
                                    dif_uart_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_is_pending(const dif_uart_t *uart, dif_uart_irq_t,
                                     bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param uart A uart handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_acknowledge_state(
    const dif_uart_t *uart, dif_uart_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param uart A uart handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_acknowledge_all(const dif_uart_t *uart);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_acknowledge(const dif_uart_t *uart, dif_uart_irq_t);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_force(const dif_uart_t *uart, dif_uart_irq_t,
                                const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_uart_irq_disable_all()` and `dif_uart_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_uart_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_get_enabled(const dif_uart_t *uart, dif_uart_irq_t,
                                      dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_set_enabled(const dif_uart_t *uart, dif_uart_irq_t,
                                      dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param uart A uart handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_disable_all(const dif_uart_t *uart,
                                      dif_uart_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param uart A uart handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_restore_all(
    const dif_uart_t *uart, const dif_uart_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_UART_AUTOGEN_H_
