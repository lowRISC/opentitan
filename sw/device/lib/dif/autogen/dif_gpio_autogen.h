// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_GPIO_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_GPIO_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/gpio/doc/">GPIO</a> Device Interface Functions
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
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_init(mmio_region_t base_addr, dif_gpio_t *gpio);

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
 */
typedef enum dif_gpio_irq {
  /**
   * Raised if any of GPIO pin detects configured interrupt mode
   */
  kDifGpioIrqGpio0 = 0,
  kDifGpioIrqGpio1 = 1,
  kDifGpioIrqGpio2 = 2,
  kDifGpioIrqGpio3 = 3,
  kDifGpioIrqGpio4 = 4,
  kDifGpioIrqGpio5 = 5,
  kDifGpioIrqGpio6 = 6,
  kDifGpioIrqGpio7 = 7,
  kDifGpioIrqGpio8 = 8,
  kDifGpioIrqGpio9 = 9,
  kDifGpioIrqGpio10 = 10,
  kDifGpioIrqGpio11 = 11,
  kDifGpioIrqGpio12 = 12,
  kDifGpioIrqGpio13 = 13,
  kDifGpioIrqGpio14 = 14,
  kDifGpioIrqGpio15 = 15,
  kDifGpioIrqGpio16 = 16,
  kDifGpioIrqGpio17 = 17,
  kDifGpioIrqGpio18 = 18,
  kDifGpioIrqGpio19 = 19,
  kDifGpioIrqGpio20 = 20,
  kDifGpioIrqGpio21 = 21,
  kDifGpioIrqGpio22 = 22,
  kDifGpioIrqGpio23 = 23,
  kDifGpioIrqGpio24 = 24,
  kDifGpioIrqGpio25 = 25,
  kDifGpioIrqGpio26 = 26,
  kDifGpioIrqGpio27 = 27,
  kDifGpioIrqGpio28 = 28,
  kDifGpioIrqGpio29 = 29,
  kDifGpioIrqGpio30 = 30,
  kDifGpioIrqGpio31 = 31,
} dif_gpio_irq_t;

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
dif_result_t dif_gpio_irq_get_type(const dif_gpio_t *gpio, dif_gpio_irq_t irq,
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
dif_result_t dif_gpio_irq_is_pending(const dif_gpio_t *gpio, dif_gpio_irq_t irq,
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
dif_result_t dif_gpio_irq_acknowledge(const dif_gpio_t *gpio,
                                      dif_gpio_irq_t irq);

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
dif_result_t dif_gpio_irq_force(const dif_gpio_t *gpio, dif_gpio_irq_t irq,
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
dif_result_t dif_gpio_irq_get_enabled(const dif_gpio_t *gpio,
                                      dif_gpio_irq_t irq, dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param gpio A gpio handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_gpio_irq_set_enabled(const dif_gpio_t *gpio,
                                      dif_gpio_irq_t irq, dif_toggle_t state);

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
