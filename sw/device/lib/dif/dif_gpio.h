// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_GPIO_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_GPIO_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Configuration for initializing a GPIO device.
 */
typedef struct dif_gpio_config { mmio_region_t base_addr; } dif_gpio_config_t;

/**
 * Internal state of a GPIO device.
 *
 * Instances of this struct must be initialized by `dif_gpio_init()` before
 * being passed to other functions.
 */
typedef struct dif_gpio { mmio_region_t base_addr; } dif_gpio_t;

/**
 * Generic return codes for the functions in this library.
 */
typedef enum dif_gpio_result {
  /**
   * The function succeeded.
   */
  kDifGpioOk,
  /**
   * The function failed a non-specific assertion.
   *
   * This error is not recoverable.
   */
  kDifGpioError,
  /**
   * There is a problem with the argument(s) to the function.
   *
   * This return code is only returned before the function has any side effects.
   *
   * This error is recoverable and the operation can be retried after correcting
   * the problem with the argument(s).
   */
  kDifGpioBadArg,

} dif_gpio_result_t;

/**
 * Set of allowed interrupt trigger configurations.
 */
typedef enum dif_gpio_irq {
  kDifGpioIrqEdgeRising,
  kDifGpioIrqEdgeFalling,
  kDifGpioIrqLevelLow,
  kDifGpioIrqLevelHigh,
  kDifGpioIrqEdgeRisingFalling,
  kDifGpioIrqEdgeRisingLevelLow,
  kDifGpioIrqEdgeFallingLevelHigh,
} dif_gpio_irq_t;

/**
 * Initialize a GPIO device using `config` and return its internal state.
 *
 * A particular GPIO device must first be initialized by this function
 * before calling other functions of this library.
 *
 * @param config Configuration for initializing a GPIO device.
 * @param gpio GPIO instance that will store the internal state of the
 * initialized GPIO device.
 * @return `kDifGpioBadArg` if `config` or `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_init(const dif_gpio_config_t *config,
                                dif_gpio_t *gpio);

/**
 * Reset GPIO device.
 *
 * Resets the given GPIO device by setting its configuration registers to
 * reset values. Disables interrupts, output, and input filter.
 *
 * @param gpio GPIO instance
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_reset(const dif_gpio_t *gpio);

/**
 * Read from all pins.
 *
 * The value returned by this function is independent of the output enable
 * setting and includes the effects of the input noise filter and the load on
 * the pins.
 *
 * @param gpio GPIO instance.
 * @param pin_values Pin values.
 * @return `kDifGpioBadArg` if `gpio` or `pin_values` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_all_read(const dif_gpio_t *gpio,
                                    uint32_t *pin_values);

/**
 * Read from a pin.
 *
 * The value returned by this function is independent of the output enable
 * setting and includes the effects of the input noise filter and the load on
 * the pin.
 *
 * @param gpio GPIO instance.
 * @param index Zero-based index of the pin to read from.
 * @param pin_value Pin value.
 * @return `kDifGpioBadArg` if `gpio` or `pin_values` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_pin_read(const dif_gpio_t *gpio, uint32_t index,
                                    bool *pin_value);

/**
 * Write to all pins.
 *
 * The actual values on the pins depend on the output enable setting.
 *
 * @param gpio GPIO instance.
 * @param val Value to write.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_all_write(const dif_gpio_t *gpio, uint32_t val);

/**
 * Write to a pin.
 *
 * The actual value on the pin depends on the output enable setting.
 *
 * @param gpio GPIO instance.
 * @param index Zero-based index of the pin to write to.
 * @param val Value to write.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_pin_write(const dif_gpio_t *gpio, uint32_t index,
                                     bool val);

/**
 * Write to the pins identified by a mask.
 *
 * The actual values on the pins depend on the output enable setting.
 *
 * @param gpio GPIO instance
 * @param mask Mask that identifies the pins to write to.
 * @param val Value to write.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_masked_write(const dif_gpio_t *gpio, uint32_t mask,
                                        uint32_t val);

/**
 * Set output modes of all pins.
 *
 * Setting `val[i]` to 1 enables output mode for pin `i`.
 *
 * @param gpio GPIO instance.
 * @param val Output modes of the pins.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_output_mode_all_set(const dif_gpio_t *gpio,
                                               uint32_t val);

/**
 * Set output mode of a pin.
 *
 * Setting `val` to `true` enables output mode for the pin.
 *
 * @param gpio GPIO instance
 * @param index Zero-based index of the pin.
 * @param val Output mode of the pin.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_output_mode_pin_set(const dif_gpio_t *gpio,
                                               uint32_t index, bool val);

/**
 * Set the output modes of the pins identified by a mask.
 *
 * Setting `val[i]` to 1 enables output mode for pin `i`.
 *
 * @param gpio GPIO instance
 * @param mask Mask that identifies the pins whose output modes will be set.
 * @param val Output modes of the pins.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_output_mode_masked_set(const dif_gpio_t *gpio,
                                                  uint32_t mask, uint32_t val);

/**
 * Test the reporting of the interrupt of a pin.
 *
 * Sets the corresponding bit in the interrupt state register. The level of
 * the interrupt output to the processor depends on the interrupt enable
 * register.
 *
 * @param gpio GPIO instance.
 * @param index Zero-based index of the pin.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_pin_test(const dif_gpio_t *gpio, uint32_t index);

/**
 * Read the interrupt states of all pins.
 *
 * @param gpio GPIO instance.
 * @param interrupt_states Interrupt states of all pins.
 * @return `kDifGpioBadArg` if `gpio` or `interrupt_states` is
 * `NULL`, `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_all_read(const dif_gpio_t *gpio,
                                        uint32_t *interrupt_states);

/**
 * Read the interrupt state of a pin.
 *
 * @param gpio GPIO instance.
 * @param index Zero-based index of the pin.
 * @param interrupt_state Interrupt state of the pin. True if there is a pending
 * interrupt, false otherwise.
 * @return `kDifGpioBadArg` if `gpio` or `interrupt_state` is
 * `NULL`, `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_pin_read(const dif_gpio_t *gpio, uint32_t index,
                                        bool *interrupt_state);

/**
 * Clear the interrupt of a pin.
 *
 * @param gpio GPIO instance.
 * @param index Zero-based index of the pin.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_pin_clear(const dif_gpio_t *gpio,
                                         uint32_t index);

/**
 * Enable noise filter for GPIO inputs.
 *
 * Setting `mask[i]` to 1 enables input noise filter for pin `i`. If enabled,
 * changes in the pin value will be ignored unless stable for 16 cycles.
 *
 * @param gpio GPIO instance.
 * @param mask Mask that identifies the pins for which input noise filter will
 * be enabled.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_input_noise_filter_masked_enable(
    const dif_gpio_t *gpio, uint32_t mask);

/**
 * Disable noise filter for GPIO inputs.
 *
 * Setting `mask[i]` to 1 disables input noise filter for pin `i`.
 *
 * @param gpio GPIO instance.
 * @param mask Mask that identifies the pins for which input noise filter will
 * be disabled.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_input_noise_filter_masked_disable(
    const dif_gpio_t *gpio, uint32_t mask);

/**
 * Enable interrupts for GPIO inputs.
 *
 * Setting `mask[i]` to 1 enables detection of interrupt events for pin `i`.
 * There are four types of interrupts per pin: rising-edge, falling-edge,
 * high-level, and low-level. At least one of them must be enabled to generate
 * interrupts.
 *
 * @param gpio GPIO instance.
 * @param mask Mask that identifies the pins for which interrupts will be
 * enabled.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_masked_enable(const dif_gpio_t *gpio,
                                             uint32_t mask);

/**
 * Disable interrupts for GPIO inputs.
 *
 * Setting `mask[i]` to 1 disables detection of interrupt events for pin `i`.
 *
 * @param gpio GPIO instance.
 * @param mask Mask that identifies the pins for which interrupts will be
 * disabled.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_masked_disable(const dif_gpio_t *gpio,
                                              uint32_t mask);

/**
 * Disable all interrupt triggers for GPIO inputs.
 *
 * This function disables all interrupt triggers, i.e. rising-edge,
 * falling-edge, level-high, and level-low, for the pins given by the mask.
 *
 * @param gpio GPIO instance.
 * @param mask Mask that identifies the pins whose interrupt triggers will be
 * disabled.
 * @return `kDifGpioBadArg` if `gpio` is `NULL`,
 * `kDifGpioOk` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_trigger_masked_disable(const dif_gpio_t *gpio,
                                                      uint32_t mask);

/**
 * Configure interrupt triggers for GPIO inputs.
 *
 * This function configures interrupt triggers, i.e. rising-edge, falling-edge,
 * level-high, and level-low, for the pins given by the mask. Note that
 * interrupt of the pin must also be enabled to generate interrupts.
 *
 * @param gpio GPIO instance.
 * @param mask Mask that identifies the pins whose interrupt triggers will be
 * configured.
 * @param config New configuration of interrupt triggers.
 * @return `kDifGpioOk` if the function is successful,
 * `kDifGpioBadArg` otherwise.
 */
dif_gpio_result_t dif_gpio_irq_trigger_masked_config(const dif_gpio_t *gpio,
                                                     uint32_t mask,
                                                     dif_gpio_irq_t config);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_GPIO_H_
