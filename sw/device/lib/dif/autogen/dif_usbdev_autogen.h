// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_USBDEV_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_USBDEV_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/book/hw/ip/usbdev/">USBDEV</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "dt_usbdev.h"  // Generated.
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to usbdev.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_usbdev {
  /**
   * The base address for the usbdev hardware registers.
   */
  mmio_region_t base_addr;
} dif_usbdev_t;

/**
 * Creates a new handle for a(n) usbdev peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the usbdev peripheral.
 * @param[out] usbdev Out param for the initialized handle.
 * @return The result of the operation.
 *
 * DEPRECATED This function exists solely for the transition to
 * dt-based DIFs and will be removed in the future.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_init(mmio_region_t base_addr, dif_usbdev_t *usbdev);

/**
 * Creates a new handle for a(n) usbdev peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param dt The devicetable description of the device.
 * @param[out] usbdev Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_init_from_dt(const dt_usbdev_t *dt,
                                     dif_usbdev_t *usbdev);

/**
 * A usbdev alert type.
 */
typedef enum dif_usbdev_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifUsbdevAlertFatalFault = 0,
} dif_usbdev_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param usbdev A usbdev handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_alert_force(const dif_usbdev_t *usbdev,
                                    dif_usbdev_alert_t alert);

/**
 * A usbdev interrupt request type.
 *
 * DEPRECATED Use `dt_usbdev_irq_t` instead.
 * This enumeration exists solely for the transition to
 * dt-based interrupt numbers and will be removed in the future.
 *
 * The following are defines to keep the types consistent with DT.
 */
/**
 * Raised if a packet was received using an OUT or SETUP transaction. This
 * interrupt is directly tied to whether the RX FIFO is empty, so it should be
 * cleared only after handling the FIFO entry.
 */
#define kDifUsbdevIrqPktReceived kDtUsbdevIrqPktReceived
/**
 * Raised if a packet was sent as part of an IN transaction. This interrupt is
 * directly tied to whether a sent packet has not been acknowledged in the
 * !!in_sent register. It should be cleared only after clearing all bits in the
 * !!in_sent register.
 */
#define kDifUsbdevIrqPktSent kDtUsbdevIrqPktSent
/**
 * Raised if VBUS is lost, thus the link is disconnected.
 */
#define kDifUsbdevIrqDisconnected kDtUsbdevIrqDisconnected
/**
 * Raised if link is active but SOF was not received from host for 4.096 ms. The
 * SOF should be every 1 ms.
 */
#define kDifUsbdevIrqHostLost kDtUsbdevIrqHostLost
/**
 * Raised if the link is at SE0 longer than 3 us indicating a link reset (host
 * asserts for min 10 ms, device can react after 2.5 us).
 */
#define kDifUsbdevIrqLinkReset kDtUsbdevIrqLinkReset
/**
 * Raised if the line has signaled J for longer than 3ms and is therefore in
 * suspend state.
 */
#define kDifUsbdevIrqLinkSuspend kDtUsbdevIrqLinkSuspend
/**
 * Raised when the link becomes active again after being suspended.
 */
#define kDifUsbdevIrqLinkResume kDtUsbdevIrqLinkResume
/**
 * Raised when the Available OUT Buffer FIFO is empty and the device interface
 * is enabled. This interrupt is directly tied to the FIFO status, so the
 * Available OUT Buffer FIFO must be provided with a free buffer before the
 * interrupt can be cleared.
 */
#define kDifUsbdevIrqAvOutEmpty kDtUsbdevIrqAvOutEmpty
/**
 * Raised when the RX FIFO is full and the device interface is enabled. This
 * interrupt is directly tied to the FIFO status, so the RX FIFO must have an
 * entry removed before the interrupt is cleared. If the condition is not
 * cleared, the interrupt can re-assert.
 */
#define kDifUsbdevIrqRxFull kDtUsbdevIrqRxFull
/**
 * Raised if a write was done to either the Available OUT Buffer FIFO or the
 * Available SETUP Buffer FIFO when the FIFO was full.
 */
#define kDifUsbdevIrqAvOverflow kDtUsbdevIrqAvOverflow
/**
 * Raised if a packet to an IN endpoint started to be received but was then
 * dropped due to an error. After transmitting the IN payload, the USB device
 * expects a valid ACK handshake packet. This error is raised if either the
 * packet or CRC is invalid, leading to a NAK instead, or if a different token
 * was received.
 */
#define kDifUsbdevIrqLinkInErr kDtUsbdevIrqLinkInErr
/**
 * Raised if a CRC error occurred on a received packet.
 */
#define kDifUsbdevIrqRxCrcErr kDtUsbdevIrqRxCrcErr
/**
 * Raised if an invalid Packet IDentifier (PID) was received.
 */
#define kDifUsbdevIrqRxPidErr kDtUsbdevIrqRxPidErr
/**
 * Raised if an invalid bitstuffing was received.
 */
#define kDifUsbdevIrqRxBitstuffErr kDtUsbdevIrqRxBitstuffErr
/**
 * Raised when the USB frame number is updated with a valid SOF.
 */
#define kDifUsbdevIrqFrame kDtUsbdevIrqFrame
/**
 * Raised if VBUS is applied.
 */
#define kDifUsbdevIrqPowered kDtUsbdevIrqPowered
/**
 * Raised if a packet to an OUT endpoint started to be received but was then
 * dropped due to an error. This error is raised if the data toggle, token,
 * packet and/or CRC are invalid, or if the appropriate Available OUT Buffer
 * FIFO is empty and/or the Received Buffer FIFO is full when a packet should
 * have been received.
 */
#define kDifUsbdevIrqLinkOutErr kDtUsbdevIrqLinkOutErr
/**
 * Raised when the Available SETUP Buffer FIFO is empty and the device interface
 * is enabled. This interrupt is directly tied to the FIFO status, so the
 * Available SETUP Buffer FIFO must be provided with a free buffer before the
 * interrupt can be cleared.
 */
#define kDifUsbdevIrqAvSetupEmpty kDtUsbdevIrqAvSetupEmpty

// DEPRECATED This typedef exists solely for the transition to
// dt-based interrupt numbers and will be removed in the future.
typedef dt_usbdev_irq_t dif_usbdev_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_usbdev_irq_get_state()`
 * and `dif_usbdev_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_usbdev_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param usbdev A usbdev handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_get_type(const dif_usbdev_t *usbdev,
                                     dif_usbdev_irq_t, dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param usbdev A usbdev handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_get_state(
    const dif_usbdev_t *usbdev, dif_usbdev_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param usbdev A usbdev handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_is_pending(const dif_usbdev_t *usbdev,
                                       dif_usbdev_irq_t, bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param usbdev A usbdev handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_acknowledge_state(
    const dif_usbdev_t *usbdev, dif_usbdev_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param usbdev A usbdev handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_acknowledge_all(const dif_usbdev_t *usbdev);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param usbdev A usbdev handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_acknowledge(const dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param usbdev A usbdev handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_force(const dif_usbdev_t *usbdev, dif_usbdev_irq_t,
                                  const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_usbdev_irq_disable_all()` and `dif_usbdev_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_usbdev_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param usbdev A usbdev handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_get_enabled(const dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t, dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param usbdev A usbdev handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_set_enabled(const dif_usbdev_t *usbdev,
                                        dif_usbdev_irq_t, dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param usbdev A usbdev handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_disable_all(
    const dif_usbdev_t *usbdev, dif_usbdev_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param usbdev A usbdev handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_usbdev_irq_restore_all(
    const dif_usbdev_t *usbdev,
    const dif_usbdev_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_USBDEV_AUTOGEN_H_
