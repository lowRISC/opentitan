// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_UART_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_UART_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/uart/doc/">UART</a> Device Interface Functions
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
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_init(mmio_region_t base_addr, dif_uart_t *uart);

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
 */
typedef enum dif_uart_irq {
  /**
   * Raised if the transmit FIFO is past the high-water mark.
   */
  kDifUartIrqTxWatermark = 0,
  /**
   * Raised if the receive FIFO is past the high-water mark.
   */
  kDifUartIrqRxWatermark = 1,
  /**
   * Raised if the transmit FIFO has emptied and no transmit is ongoing.
   */
  kDifUartIrqTxEmpty = 2,
  /**
   * Raised if the receive FIFO has overflowed.
   */
  kDifUartIrqRxOverflow = 3,
  /**
   * Raised if a framing error has been detected on receive.
   */
  kDifUartIrqRxFrameErr = 4,
  /**
   * Raised if break condition has been detected on receive.
   */
  kDifUartIrqRxBreakErr = 5,
  /**
   * Raised if RX FIFO has characters remaining in the FIFO without being
   * retrieved for the programmed time period.
   */
  kDifUartIrqRxTimeout = 6,
  /**
   * Raised if the receiver has detected a parity error.
   */
  kDifUartIrqRxParityErr = 7,
} dif_uart_irq_t;

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
dif_result_t dif_uart_irq_get_type(const dif_uart_t *uart, dif_uart_irq_t irq,
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
dif_result_t dif_uart_irq_is_pending(const dif_uart_t *uart, dif_uart_irq_t irq,
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
dif_result_t dif_uart_irq_acknowledge(const dif_uart_t *uart,
                                      dif_uart_irq_t irq);

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
dif_result_t dif_uart_irq_force(const dif_uart_t *uart, dif_uart_irq_t irq,
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
dif_result_t dif_uart_irq_get_enabled(const dif_uart_t *uart,
                                      dif_uart_irq_t irq, dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param uart A uart handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_uart_irq_set_enabled(const dif_uart_t *uart,
                                      dif_uart_irq_t irq, dif_toggle_t state);

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
