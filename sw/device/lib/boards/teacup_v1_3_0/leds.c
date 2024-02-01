// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/boards/teacup_v1_3_0/leds.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/i2c_testutils.h"

static const size_t kDefaultI2cReadTimeoutMicros = 1000;

status_t leds_read_ctrl_reg(const dif_i2c_t *i2c, uint8_t reg_addr,
                            uint8_t *data_out) {
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/1, &reg_addr,
                          /*skip_stop=*/false));
  TRY(i2c_testutils_read(i2c, kLedsDriverI2cAddr, /*byte_count=*/1, data_out,
                         kDefaultI2cReadTimeoutMicros));
  return OK_STATUS();
}

status_t leds_set_color(const dif_i2c_t *i2c, teacup_led_t led,
                        led_rgb_color_t color) {
  // Get register addresses for desired LED.
  uint8_t b_pwm_low_reg;
  uint8_t r_pwm_low_reg;
  uint8_t g_pwm_low_reg;
  switch (led) {
    case kTeacupLedDs5:
      b_pwm_low_reg = kLedBlue0LowRegAddr;
      r_pwm_low_reg = kLedRed0LowRegAddr;
      g_pwm_low_reg = kLedGreen0LowRegAddr;
      break;
    case kTeacupLedDs9:
      b_pwm_low_reg = kLedBlue1LowRegAddr;
      r_pwm_low_reg = kLedRed1LowRegAddr;
      g_pwm_low_reg = kLedGreen1LowRegAddr;
      break;
    case kTeacupLedDs10:
      b_pwm_low_reg = kLedBlue2LowRegAddr;
      r_pwm_low_reg = kLedRed2LowRegAddr;
      g_pwm_low_reg = kLedGreen2LowRegAddr;
      break;
    case kTeacupLedDs11:
      b_pwm_low_reg = kLedBlue3LowRegAddr;
      r_pwm_low_reg = kLedRed3LowRegAddr;
      g_pwm_low_reg = kLedGreen3LowRegAddr;
      break;
    default:
      return INTERNAL();
  }

  // Set PWM duty cycle for each color channel of the specified LED.
  // Blue
  uint8_t blue_data[2] = {b_pwm_low_reg, color.b};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr,
                          /*byte_count=*/sizeof(blue_data), blue_data,
                          /*skip_stop=*/false));
  // Red
  uint8_t red_data[2] = {r_pwm_low_reg, color.r};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr,
                          /*byte_count=*/sizeof(red_data), red_data,
                          /*skip_stop=*/false));
  // Green
  uint8_t green_data[2] = {g_pwm_low_reg, color.g};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr,
                          /*byte_count=*/sizeof(green_data), green_data,
                          /*skip_stop=*/false));

  // Activate PWM configurations.
  uint8_t data[2] = {kLedUpdateRegAddr, 0};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/sizeof(data),
                          data,
                          /*skip_stop=*/false));

  return OK_STATUS();
}

status_t leds_set_all_brightness(const dif_i2c_t *i2c, uint8_t brightness) {
  uint8_t data[2] = {kLedGlobalCurrentControlRegAddr, brightness};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/sizeof(data),
                          data,
                          /*skip_stop=*/false));
  return OK_STATUS();
}

status_t leds_i2c_controller_configure(const dif_i2c_t *i2c) {
  // Set control register to 0x0 to enable:
  // - Software shutdown mode (keep LEDs off until explicitly turned on)
  // - 8-bit (PWM resolution)
  // - 16MHz (max oscillator clock frequency)
  uint8_t data[2] = {kLedsControlRegAddr, 0};
  uint8_t reg_val = 0;
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/sizeof(data),
                          data,
                          /*skip_stop=*/false));
  TRY(leds_read_ctrl_reg(i2c, kLedsControlRegAddr, &reg_val));
  LOG_INFO("Control Reg = 0x%02x", reg_val);

  // Set global current control to ~30%.
  data[0] = kLedGlobalCurrentControlRegAddr;
  data[1] = (uint8_t)((float)0xFF * 30.0 / 100.0);
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/sizeof(data),
                          data,
                          /*skip_stop=*/false));
  TRY(leds_read_ctrl_reg(i2c, kLedGlobalCurrentControlRegAddr, &reg_val));
  LOG_INFO("Global Current Control Reg = 0x%02x", reg_val);

  // Set each PWM channel's current control to 100%.
  data[0] = kLedChannel0ScalingRegAddr;
  data[1] = 0xFF;
  for (size_t i = 0; i < 12; ++i) {
    TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr,
                            /*byte_count=*/sizeof(data), data,
                            /*skip_stop=*/false));
    TRY(leds_read_ctrl_reg(i2c, data[0], &reg_val));
    LOG_INFO("LED Channel %d Scaling Reg = 0x%02x", i, reg_val);
    data[0]++;
  }

  return OK_STATUS();
}

status_t leds_turn_all_off(const dif_i2c_t *i2c) {
  LOG_INFO("Turning off LEDs via software shutdown bit ...");
  uint8_t ctrl_reg_val = 0;
  TRY(leds_read_ctrl_reg(i2c, kLedsControlRegAddr, &ctrl_reg_val));
  uint8_t data[2] = {kLedsControlRegAddr, ctrl_reg_val & ~0x1};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/sizeof(data),
                          data,
                          /*skip_stop=*/false));
  return OK_STATUS();
}

status_t leds_turn_all_on(const dif_i2c_t *i2c) {
  LOG_INFO("Turning on LEDs via software shutdown bit ...");
  uint8_t ctrl_reg_val = 0;
  TRY(leds_read_ctrl_reg(i2c, kLedsControlRegAddr, &ctrl_reg_val));
  uint8_t data[2] = {kLedsControlRegAddr, ctrl_reg_val | 0x1};
  TRY(i2c_testutils_write(i2c, kLedsDriverI2cAddr, /*byte_count=*/sizeof(data),
                          data,
                          /*skip_stop=*/false));
  return OK_STATUS();
}
