// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_GPIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_GPIO_H_

#include <stddef.h>
#include <stdint.h>

#include "hw/top/dt/gpio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/gpio_regs.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Number of pins.
   *
   * This constant is used to check that arguments of type `gpio_pin_t` are
   * within bounds.
   */
  kGpioNumPins = 32,
};

/**
 * A GPIO pin index, ranging from 0 to `kGpioNumPins - 1`.
 */
typedef uint32_t gpio_pin_t;

/**
 * Reads from a pin.
 *
 * The value returned by this function is independent of the output enable
 * setting and includes the effects of the input noise filter and the load on
 * the pin.
 *
 * @param pin A GPIO pin.
 * @param[out] state Pin value.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t gpio_read(gpio_pin_t pin, bool *state);

/**
 * Writes to a pin.
 *
 * The actual value on the pin depends on the output enable setting.
 *
 * @param pin A GPIO pin.
 * @param state Value to write.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t gpio_write(gpio_pin_t pin, bool state);

/**
 * Sets output mode of a pin.
 *
 * @param pin A GPIO pin.
 * @param output Output mode of the pin. The pin is set to an output pin if
 *        `output` is `true`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t gpio_set_output_mode(gpio_pin_t pin, bool output);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_GPIO_H_
