// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_GPIO_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_GPIO_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/book/hw/ip/gpio/">GPIO</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "dt_gpio.h"  // Generated.
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to gpio.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_gpio {
  /**
   * The base address for the gpio hardware registers.
   */
  mmio_region_t base_addr;
} dif_gpio_t;

/**
 * Creates a new handle for a(n) gpio peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the gpio peripheral.
 * @param[out] gpio Out param for the initialized handle.
 * @return The result of the operation.
 *
 * DEPRECATED This function exists solely for the transition to
 * dt-based DIFs and will be removed in the future.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_init(mmio_region_t base_addr, dif_gpio_t *gpio);

/**
 * Creates a new handle for a(n) gpio peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param dt The devicetable description of the device.
 * @param[out] gpio Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_init_from_dt(const dt_gpio_t *dt, dif_gpio_t *gpio);

/**
 * A gpio alert type.
 */
typedef enum dif_gpio_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifGpioAlertFatalFault = 0,
} dif_gpio_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param gpio A gpio handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_alert_force(const dif_gpio_t *gpio,
                                  dif_gpio_alert_t alert);

/**
 * A gpio interrupt request type.
 *
 * DEPRECATED Use `dt_gpio_irq_t` instead.
 * This enumeration exists solely for the transition to
 * dt-based interrupt numbers and will be removed in the future.
 *
 * The following are defines to keep the types consistent with DT.
 */
/**
 * Raised if any of GPIO pin detects configured interrupt mode
 */
#define kDifGpioIrqGpio0 kDtGpioIrqGpio0
#define kDifGpioIrqGpio1 kDtGpioIrqGpio1
#define kDifGpioIrqGpio2 kDtGpioIrqGpio2
#define kDifGpioIrqGpio3 kDtGpioIrqGpio3
#define kDifGpioIrqGpio4 kDtGpioIrqGpio4
#define kDifGpioIrqGpio5 kDtGpioIrqGpio5
#define kDifGpioIrqGpio6 kDtGpioIrqGpio6
#define kDifGpioIrqGpio7 kDtGpioIrqGpio7
#define kDifGpioIrqGpio8 kDtGpioIrqGpio8
#define kDifGpioIrqGpio9 kDtGpioIrqGpio9
#define kDifGpioIrqGpio10 kDtGpioIrqGpio10
#define kDifGpioIrqGpio11 kDtGpioIrqGpio11
#define kDifGpioIrqGpio12 kDtGpioIrqGpio12
#define kDifGpioIrqGpio13 kDtGpioIrqGpio13
#define kDifGpioIrqGpio14 kDtGpioIrqGpio14
#define kDifGpioIrqGpio15 kDtGpioIrqGpio15
#define kDifGpioIrqGpio16 kDtGpioIrqGpio16
#define kDifGpioIrqGpio17 kDtGpioIrqGpio17
#define kDifGpioIrqGpio18 kDtGpioIrqGpio18
#define kDifGpioIrqGpio19 kDtGpioIrqGpio19
#define kDifGpioIrqGpio20 kDtGpioIrqGpio20
#define kDifGpioIrqGpio21 kDtGpioIrqGpio21
#define kDifGpioIrqGpio22 kDtGpioIrqGpio22
#define kDifGpioIrqGpio23 kDtGpioIrqGpio23
#define kDifGpioIrqGpio24 kDtGpioIrqGpio24
#define kDifGpioIrqGpio25 kDtGpioIrqGpio25
#define kDifGpioIrqGpio26 kDtGpioIrqGpio26
#define kDifGpioIrqGpio27 kDtGpioIrqGpio27
#define kDifGpioIrqGpio28 kDtGpioIrqGpio28
#define kDifGpioIrqGpio29 kDtGpioIrqGpio29
#define kDifGpioIrqGpio30 kDtGpioIrqGpio30
#define kDifGpioIrqGpio31 kDtGpioIrqGpio31

// DEPRECATED This typedef exists solely for the transition to
// dt-based interrupt numbers and will be removed in the future.
typedef dt_gpio_irq_t dif_gpio_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_gpio_irq_get_state()`
 * and `dif_gpio_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_gpio_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_get_type(const dif_gpio_t *gpio, dif_gpio_irq_t,
                                   dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param gpio A gpio handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_get_state(const dif_gpio_t *gpio,
                                    dif_gpio_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_is_pending(const dif_gpio_t *gpio, dif_gpio_irq_t,
                                     bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param gpio A gpio handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_acknowledge_state(
    const dif_gpio_t *gpio, dif_gpio_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param gpio A gpio handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_acknowledge_all(const dif_gpio_t *gpio);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_acknowledge(const dif_gpio_t *gpio, dif_gpio_irq_t);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_force(const dif_gpio_t *gpio, dif_gpio_irq_t,
                                const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_gpio_irq_disable_all()` and `dif_gpio_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_gpio_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_get_enabled(const dif_gpio_t *gpio, dif_gpio_irq_t,
                                      dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_set_enabled(const dif_gpio_t *gpio, dif_gpio_irq_t,
                                      dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param gpio A gpio handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_disable_all(const dif_gpio_t *gpio,
                                      dif_gpio_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param gpio A gpio handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_restore_all(
    const dif_gpio_t *gpio, const dif_gpio_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_GPIO_AUTOGEN_H_
