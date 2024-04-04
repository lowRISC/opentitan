// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BOARDS_TEACUP_V1_3_0_LEDS_H_
#define OPENTITAN_SW_DEVICE_LIB_BOARDS_TEACUP_V1_3_0_LEDS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_i2c.h"

/**
 * Defined Constants.
 */
enum {
  // Teacup LED Controller
  kLedsDriverI2cAddr = 0x34,

  // Teacup LED Controller Registers
  kLedsControlRegAddr = 0x00,
  kLedUpdateRegAddr = 0x49,
  kLedChannel0ScalingRegAddr = 0x4D,
  kLedGlobalCurrentControlRegAddr = 0x6E,

  // LED DS5
  kLedBlue0LowRegAddr = 0x07,
  kLedRed0LowRegAddr = 0x09,
  kLedGreen0LowRegAddr = 0x0B,

  // LED DS9
  kLedBlue1LowRegAddr = 0x0D,
  kLedRed1LowRegAddr = 0x0F,
  kLedGreen1LowRegAddr = 0x11,

  // LED DS10
  kLedBlue2LowRegAddr = 0x13,
  kLedRed2LowRegAddr = 0x15,
  kLedGreen2LowRegAddr = 0x17,

  // LED DS11
  kLedBlue3LowRegAddr = 0x19,
  kLedRed3LowRegAddr = 0x1B,
  kLedGreen3LowRegAddr = 0x1D,

  // Other
  kNumTeacupLeds = 4,
};

/**
 * Teacup RGB LEDs.
 */
typedef enum teacup_led {
  kTeacupLedDs5 = 0,
  kTeacupLedDs9 = 1,
  kTeacupLedDs10 = 2,
  kTeacupLedDs11 = 3,
} teacup_led_t;

/**
 * LED RGB color value.
 */
typedef struct led_rgb_color {
  uint8_t r;
  uint8_t g;
  uint8_t b;
} led_rgb_color_t;

/**
 * Reads the teacup LED controller's control register.
 *
 * @param i2c I2C handle to communicate with the I2C LED controller.
 * @param reg_addr Address of the I2C LED controller to read.
 * @param[out] data_out Data read from the I2C LED controller.
 */
OT_WARN_UNUSED_RESULT
status_t leds_read_ctrl_reg(const dif_i2c_t *i2c, uint8_t reg_addr,
                            uint8_t *data_out);

/**
 * Sets the color for a specific teacup LED.
 *
 * @param i2c I2C handle to communicate with the I2C LED controller.
 * @param led The teacup LED to configure.
 * @param color The color to set the LED to.
 */
OT_WARN_UNUSED_RESULT
status_t leds_set_color(const dif_i2c_t *i2c, teacup_led_t led,
                        led_rgb_color_t color);

/**
 * Sets the brightness (global current control) of all LEDs on the teacup board.
 *
 * @param i2c I2C handle to communicate with the I2C LED controller.
 * @param brightness The brightness value, in [0, 255], to set the LED to.
 */
OT_WARN_UNUSED_RESULT
status_t leds_set_all_brightness(const dif_i2c_t *i2c, uint8_t brightness);

/**
 * Configures the I2C LED controller on the teacup board.
 *
 * @param i2c I2C handle to communicate with the I2C LED controller.
 */
OT_WARN_UNUSED_RESULT
status_t leds_i2c_controller_configure(const dif_i2c_t *i2c);

/**
 * Turns all LEDs off, on the teacup board.
 *
 * @param i2c I2C handle to communicate with the I2C LED controller.
 */
OT_WARN_UNUSED_RESULT
status_t leds_turn_all_off(const dif_i2c_t *i2c);

/**
 * Turns all LEDs on, on the teacup board.
 *
 * @param i2c I2C handle to communicate with the I2C LED controller.
 */
OT_WARN_UNUSED_RESULT
status_t leds_turn_all_on(const dif_i2c_t *i2c);

#endif  // OPENTITAN_SW_DEVICE_LIB_BOARDS_TEACUP_V1_3_0_LEDS_H_
