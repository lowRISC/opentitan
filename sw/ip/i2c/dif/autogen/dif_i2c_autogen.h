// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_I2C_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_I2C_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/i2c/doc/">I2C</a> Device Interface Functions
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
 * A handle to i2c.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_i2c {
  /**
   * The base address for the i2c hardware registers.
   */
  mmio_region_t base_addr;
} dif_i2c_t;

/**
 * Creates a new handle for a(n) i2c peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the i2c peripheral.
 * @param[out] i2c Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_init(mmio_region_t base_addr, dif_i2c_t *i2c);

/**
 * A i2c alert type.
 */
typedef enum dif_i2c_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifI2cAlertFatalFault = 0,
} dif_i2c_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param i2c A i2c handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_alert_force(const dif_i2c_t *i2c, dif_i2c_alert_t alert);

/**
 * A i2c interrupt request type.
 */
typedef enum dif_i2c_irq {
  /**
   * Host mode interrupt: raised when the FMT FIFO depth is less than the low
   * threshold.
   */
  kDifI2cIrqFmtThreshold = 0,
  /**
   * Host mode interrupt: raised if the RX FIFO is greater than the high
   * threshold.
   */
  kDifI2cIrqRxThreshold = 1,
  /**
   * Host mode interrupt: raised if the FMT FIFO has overflowed.
   */
  kDifI2cIrqFmtOverflow = 2,
  /**
   * Host mode interrupt: raised if the RX FIFO has overflowed.
   */
  kDifI2cIrqRxOverflow = 3,
  /**
   * Host mode interrupt: raised if there is no ACK in response to an address or
   * data write
   */
  kDifI2cIrqNak = 4,
  /**
   * Host mode interrupt: raised if the SCL line drops early (not supported
   * without clock synchronization).
   */
  kDifI2cIrqSclInterference = 5,
  /**
   * Host mode interrupt: raised if the SDA line goes low when host is trying to
   * assert high
   */
  kDifI2cIrqSdaInterference = 6,
  /**
   * Host mode interrupt: raised if target stretches the clock beyond the
   * allowed timeout period
   */
  kDifI2cIrqStretchTimeout = 7,
  /**
   * Host mode interrupt: raised if the target does not assert a constant value
   * of SDA during transmission.
   */
  kDifI2cIrqSdaUnstable = 8,
  /**
   * Host and target mode interrupt. In host mode, raised if the host issues a
   * repeated START or terminates the transaction by issuing STOP. In target
   * mode, raised if the external host issues a STOP or repeated START.
   */
  kDifI2cIrqCmdComplete = 9,
  /**
   * Target mode interrupt: raised if the target is stretching clocks for a read
   * command.  This is a level status interrupt.
   */
  kDifI2cIrqTxStretch = 10,
  /**
   * Target mode interrupt: raised if TX FIFO has overflowed.
   */
  kDifI2cIrqTxOverflow = 11,
  /**
   * Target mode interrupt: raised if ACQ FIFO becomes full.  This is a level
   * status interrupt.
   */
  kDifI2cIrqAcqFull = 12,
  /**
   * Target mode interrupt: raised if STOP is received without a preceding NACK
   * during an external host read.
   */
  kDifI2cIrqUnexpStop = 13,
  /**
   * Target mode interrupt: raised if the host stops sending the clock during an
   * ongoing transaction.
   */
  kDifI2cIrqHostTimeout = 14,
} dif_i2c_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_i2c_irq_get_state()`
 * and `dif_i2c_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_i2c_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param i2c A i2c handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_get_type(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                  dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param i2c A i2c handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_get_state(const dif_i2c_t *i2c,
                                   dif_i2c_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param i2c A i2c handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_is_pending(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                    bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param i2c A i2c handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_acknowledge_state(
    const dif_i2c_t *i2c, dif_i2c_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param i2c A i2c handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_acknowledge_all(const dif_i2c_t *i2c);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param i2c A i2c handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_acknowledge(const dif_i2c_t *i2c, dif_i2c_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param i2c A i2c handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_force(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                               const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_i2c_irq_disable_all()` and `dif_i2c_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_i2c_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param i2c A i2c handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_get_enabled(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                     dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param i2c A i2c handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_set_enabled(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                     dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param i2c A i2c handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_disable_all(const dif_i2c_t *i2c,
                                     dif_i2c_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param i2c A i2c handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_irq_restore_all(
    const dif_i2c_t *i2c, const dif_i2c_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_I2C_AUTOGEN_H_
