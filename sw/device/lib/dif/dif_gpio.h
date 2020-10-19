// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_GPIO_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_GPIO_H_

/**
 * @file
 * @brief <a href="/hw/ip/gpio/doc/">GPIO</a> Device Interface Functions
 */

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 *
 * This enum may be used with `dif_gpio_toggle_vec_t` to set individual bits
 * within it; `dif_gpio_toggle_t`'s variants are guaranteed to be compatible
 * with `dif_gpio_toggle_vec_t`.
 */
typedef enum dif_gpio_toggle {
  /*
   * The "enabled" state.
   */
  kDifGpioToggleEnabled = true,
  /**
   * The "disabled" state.
   */
  kDifGpioToggleDisabled = false,
} dif_gpio_toggle_t;

/**
 * Hardware instantiation parameters for GPIO.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_gpio_params {
  /**
   * The base address for the GPIO hardware registers.
   */
  mmio_region_t base_addr;
} dif_gpio_params_t;

/**
 * A handle to GPIO.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_gpio { dif_gpio_params_t params; } dif_gpio_t;

/**
 * The result of a GPIO operation.
 */
typedef enum dif_gpio_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifGpioOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifGpioError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDifGpioBadArg = 2,
} dif_gpio_result_t;

/**
 * A GPIO interrupt request trigger.
 *
 * Each GPIO pin has an associated interrupt that can be independently
 * configured
 * to be edge and/or level sensitive. This enum defines supported configurations
 * for
 * these interrupts.
 */
typedef enum dif_gpio_irq_trigger {
  /**
   * Trigger on rising edge.
   */
  kDifGpioIrqTriggerEdgeRising,
  /**
   * Trigger on falling edge.
   */
  kDifGpioIrqTriggerEdgeFalling,
  /**
   * Trigger when input is low.
   */
  kDifGpioIrqTriggerLevelLow,
  /**
   * Trigger when input is high.
   */
  kDifGpioIrqTriggerLevelHigh,
  /**
   * Trigger on rising and falling edges.
   */
  kDifGpioIrqTriggerEdgeRisingFalling,
  /**
   * Trigger on rising edge or when the input is low.
   */
  kDifGpioIrqTriggerEdgeRisingLevelLow,
  /**
   * Trigger on falling edge or when the input is high.
   */
  kDifGpioIrqTriggerEdgeFallingLevelHigh,
} dif_gpio_irq_trigger_t;

/**
 * A GPIO pin index, ranging from 0 to 31.
 *
 * This type serves as the GPIO interrupt request type.
 */
typedef uint32_t dif_gpio_pin_t;

/**
 * State for all 32 GPIO pins, given as bit fields.
 *
 * The Nth bit represents the state of the Nth pin.
 *
 * This type is also used as a vector of `dif_gpio_toggle_t`s, to indicate
 * toggle state across all 32 pins. A set bit corresponds to
 * `kDifGpioToggleEnabled`.
 *
 * It is also used with `dif_gpio_irq_disable_all()` and
 * `dif_gpio_irq_restore_all()`.
 */
typedef uint32_t dif_gpio_state_t;

/**
 * A mask for selecting GPIO pins.
 *
 * If the Nth bit is enabled, then the Nth pin is selected by the mask.
 */
typedef uint32_t dif_gpio_mask_t;

/**
 * Creates a new handle for GPIO.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] gpio Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_init(dif_gpio_params_t params, dif_gpio_t *gpio);

/**
 * Resets a GPIO device.
 *
 * Resets the given GPIO device by setting its configuration registers to
 * reset values. Disables interrupts, output, and input filter.
 *
 * @param gpio A GPIO handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_reset(const dif_gpio_t *gpio);

/**
 * Returns whether a particular pin's interrupt is currently pending.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_is_pending(const dif_gpio_t *gpio,
                                          dif_gpio_pin_t pin, bool *is_pending);

/**
 * Returns a GPIO state representing which pins have interrupts enabled.
 *
 * @param gpio A GPIO handle.
 * @param[out] is_pending Out-param for which interrupts are pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_is_pending_all(const dif_gpio_t *gpio,
                                              dif_gpio_state_t *is_pending);

/**
 * Acknowledges a particular pin's interrupt, indicating to the hardware that it
 * has
 * been successfully serviced.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_acknowledge(const dif_gpio_t *gpio,
                                           dif_gpio_pin_t pin);

/**
 * Checks whether a particular pin's interrupt is currently enabled or disabled.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_get_enabled(const dif_gpio_t *gpio,
                                           dif_gpio_pin_t pin,
                                           dif_gpio_toggle_t *state);

/**
 * Sets whether a particular pin's interrupt is currently enabled or disabled.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_set_enabled(const dif_gpio_t *gpio,
                                           dif_gpio_pin_t pin,
                                           dif_gpio_toggle_t state);

/**
 * Sets whether a particular pin's interrupt is currently enabled or disabled.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_set_enabled_masked(const dif_gpio_t *gpio,
                                                  dif_gpio_mask_t mask,
                                                  dif_gpio_toggle_t state);

/**
 * Forces a particular pin's interrupt, causing it to be serviced as if hardware
 * had asserted it.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_force(const dif_gpio_t *gpio,
                                     dif_gpio_pin_t pin);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param gpio A GPIO handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_disable_all(const dif_gpio_t *gpio,
                                           dif_gpio_state_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_gpio_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param gpio A GPIO handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_restore_all(const dif_gpio_t *gpio,
                                           const dif_gpio_state_t *snapshot);

/**
 * Configures interrupt triggers for a set of pins.
 *
 * This function configures interrupt triggers, i.e. rising-edge, falling-edge,
 * level-high, and level-low, for the pins given by the mask. Note that
 * interrupt of the pin must also be enabled to generate interrupts.
 *
 * @param gpio A GPIO handle.
 * @param mask Mask that identifies the pins whose interrupt triggers will be
 * configured.
 * @param trigger New configuration of interrupt triggers.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_irq_set_trigger(const dif_gpio_t *gpio,
                                           dif_gpio_mask_t mask,
                                           dif_gpio_irq_trigger_t trigger);

/**
 * Reads from a pin.
 *
 * The value returned by this function is independent of the output enable
 * setting and includes the effects of the input noise filter and the load on
 * the pin.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param[out] state Pin value.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_read(const dif_gpio_t *gpio, dif_gpio_pin_t pin,
                                bool *state);

/**
 * Reads from all pins.
 *
 * The value returned by this function is independent of the output enable
 * setting and includes the effects of the input noise filter and the load on
 * the pins.
 *
 * @param gpio A GPIO handle.
 * @param[out] state Pin values.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_read_all(const dif_gpio_t *gpio,
                                    dif_gpio_state_t *state);

/**
 * Writes to a pin.
 *
 * The actual value on the pin depends on the output enable setting.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param state Value to write.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_write(const dif_gpio_t *gpio, dif_gpio_pin_t pin,
                                 bool state);

/**
 * Writes to all pins.
 *
 * The actual values on the pins depend on the output enable setting.
 *
 * @param gpio A GPIO handle.
 * @param val Value to write.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_write_all(const dif_gpio_t *gpio,
                                     dif_gpio_state_t state);

/**
 * Writes to the pins identified by a mask.
 *
 * The actual values on the pins depend on the output enable setting.
 *
 * @param gpio A GPIO handle.
 * @param mask Mask that identifies the pins to write to.
 * @param state Value to write.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_write_masked(const dif_gpio_t *gpio,
                                        dif_gpio_mask_t mask,
                                        dif_gpio_state_t state);

/**
 * Sets output enable mode of a pin.
 *
 * @param gpio A GPIO handle.
 * @param pin A GPIO pin.
 * @param state Output mode of the pin.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_output_set_enabled(const dif_gpio_t *gpio,
                                              dif_gpio_pin_t pin,
                                              dif_gpio_toggle_t state);

/**
 * Sets output modes of all pins.
 *
 * @param gpio A GPIO handle.
 * @param state Output modes of the pins.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_output_set_enabled_all(const dif_gpio_t *gpio,
                                                  dif_gpio_state_t state);

/**
 * Sets the output modes of the pins identified by a mask.
 *
 * @param gpio A GPIO handle.
 * @param mask Mask that identifies the pins whose output modes will be set.
 * @param state Output modes of the pins.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_output_set_enabled_masked(const dif_gpio_t *gpio,
                                                     dif_gpio_mask_t mask,
                                                     dif_gpio_state_t state);

/**
 * Enable noise filter for GPIO inputs.
 *
 * When enabled, changes in the pin value will be ignored unless stable
 * for 16 cycles.
 *
 * @param gpio A GPIO handle.
 * @param mask Mask that identifies pins to set the filter state of.
 * @param state The new toggle state for the filter.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_gpio_result_t dif_gpio_input_noise_filter_set_enabled(
    const dif_gpio_t *gpio, dif_gpio_mask_t mask, dif_gpio_toggle_t state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_GPIO_H_
