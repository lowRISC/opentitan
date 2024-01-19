// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * OT Peripheral Handles.
 */
static dif_i2c_t i2c;
static dif_pinmux_t pinmux;

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
typedef struct rgb_color {
  uint8_t r;
  uint8_t g;
  uint8_t b;
} rgb_color_t;

/**
 * Defined Constants.
 */
enum {
  // Teacup LED Controller
  kDeviceAddr = 0x34,

  // Teacup LED Controller Registers
  kControlRegAddr = 0x00,
  kUpdateRegAddr = 0x49,
  kLedChannel0ScalingRegAddr = 0x4D,
  kGlobalCurrentControlRegAddr = 0x6E,

  // LED DS5
  // Blue
  kPwmReg0LowAddr = 0x07,
  // Red
  kPwmReg1LowAddr = 0x09,
  // Green
  kPwmReg2LowAddr = 0x0B,

  // LED DS9
  // Blue
  kPwmReg3LowAddr = 0x0D,
  // Red
  kPwmReg4LowAddr = 0x0F,
  // Green
  kPwmReg5LowAddr = 0x11,

  // LED DS10
  // Blue
  kPwmReg6LowAddr = 0x13,
  // Red
  kPwmReg7LowAddr = 0x15,
  // Green
  kPwmReg8LowAddr = 0x17,

  // LED DS11
  // Blue
  kPwmReg9LowAddr = 0x19,
  // Red
  kPwmReg10LowAddr = 0x1B,
  // Green
  kPwmReg11LowAddr = 0x1D,

  // Other
  kDefaultTimeoutMicros = 1000,
};

static rgb_color_t kColorBlue = {
    .r = 0x33,
    .g = 0x69,
    .b = 0xE8,
};

static rgb_color_t kColorRed = {
    .r = 0xD5,
    .g = 0x0F,
    .b = 0x25,
};

static rgb_color_t kColorYellow = {
    .r = 0xEE,
    .g = 0xB2,
    .b = 0x11,
};

static rgb_color_t kColorGreen = {
    .r = 0x00,
    .g = 0x99,
    .b = 0x25,
};

static status_t peripheral_init(void) {
  // Initialize DIFs.
  TRY(dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));

  // Initialize pinmux.
  TRY(dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInI2c0Scl,
                              kTopEarlgreyPinmuxInselIob9));
  TRY(dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInI2c0Sda,
                              kTopEarlgreyPinmuxInselIob10));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob9,
                               kTopEarlgreyPinmuxOutselI2c0Scl));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob10,
                               kTopEarlgreyPinmuxOutselI2c0Sda));

  return OK_STATUS();
}

static status_t read_led_ctrl_reg(uint8_t reg_addr, uint8_t *data_out) {
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/1, &reg_addr,
                          /*skip_stop=*/false));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, /*byte_count=*/1, data_out,
                         kDefaultTimeoutMicros));
  return OK_STATUS();
}

static status_t set_led_ctrl_color(teacup_led_t led, const rgb_color_t *color) {
  // Get register addresses for desired LED.
  uint8_t b_pwm_low_reg;
  uint8_t r_pwm_low_reg;
  uint8_t g_pwm_low_reg;
  switch (led) {
    case kTeacupLedDs5:
      b_pwm_low_reg = kPwmReg0LowAddr;
      r_pwm_low_reg = kPwmReg1LowAddr;
      g_pwm_low_reg = kPwmReg2LowAddr;
      break;
    case kTeacupLedDs9:
      b_pwm_low_reg = kPwmReg3LowAddr;
      r_pwm_low_reg = kPwmReg4LowAddr;
      g_pwm_low_reg = kPwmReg5LowAddr;
      break;
    case kTeacupLedDs10:
      b_pwm_low_reg = kPwmReg6LowAddr;
      r_pwm_low_reg = kPwmReg7LowAddr;
      g_pwm_low_reg = kPwmReg8LowAddr;
      break;
    case kTeacupLedDs11:
      b_pwm_low_reg = kPwmReg9LowAddr;
      r_pwm_low_reg = kPwmReg10LowAddr;
      g_pwm_low_reg = kPwmReg11LowAddr;
      break;
    default:
      return INTERNAL();
  }

  // Set PWM duty cycle for each color channel of the specified LED.
  // Blue
  uint8_t blue_data[2] = {b_pwm_low_reg, color->b};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(blue_data),
                          blue_data,
                          /*skip_stop=*/false));
  // Red
  uint8_t red_data[2] = {r_pwm_low_reg, color->r};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(red_data),
                          red_data,
                          /*skip_stop=*/false));
  // Green
  uint8_t green_data[2] = {g_pwm_low_reg, color->g};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(green_data),
                          green_data,
                          /*skip_stop=*/false));

  // Activate PWM configurations.
  uint8_t data[2] = {kUpdateRegAddr, 0};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(data), data,
                          /*skip_stop=*/false));

  return OK_STATUS();
}

static status_t config_i2c_led_controller(void) {
  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));
  TRY(i2c_testutils_set_speed(&i2c, kDifI2cSpeedFastPlus));

  // Set control register to 0x0 to enable:
  // - Software shutdown mode (keep LEDs off until explicitly turned on)
  // - 8-bit (PWM resolution)
  // - 16MHz (max oscillator clock frequency)
  uint8_t data[2] = {kControlRegAddr, 0};
  uint8_t reg_val = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(data), data,
                          /*skip_stop=*/false));
  TRY(read_led_ctrl_reg(kControlRegAddr, &reg_val));
  LOG_INFO("Control Reg = 0x%02x", reg_val);

  // Set global current control to ~30%.
  data[0] = kGlobalCurrentControlRegAddr;
  data[1] = 0x55;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(data), data,
                          /*skip_stop=*/false));
  TRY(read_led_ctrl_reg(kGlobalCurrentControlRegAddr, &reg_val));
  LOG_INFO("Global Current Control Reg = 0x%02x", reg_val);

  // Set each PWM channel's current control to 100%.
  data[0] = kLedChannel0ScalingRegAddr;
  data[1] = 0xFF;
  for (size_t i = 0; i < 12; ++i) {
    TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(data),
                            data,
                            /*skip_stop=*/false));
    TRY(read_led_ctrl_reg(data[0], &reg_val));
    LOG_INFO("LED Channel %d Scaling Reg = 0x%02x", i, reg_val);
    data[0]++;
  }

  return OK_STATUS();
}

static status_t turn_off_leds(void) {
  LOG_INFO("Turning off LEDs via software shutdown bit ...");
  uint8_t ctrl_reg_val = 0;
  TRY(read_led_ctrl_reg(kControlRegAddr, &ctrl_reg_val));
  uint8_t data[2] = {kControlRegAddr, ctrl_reg_val & ~0x1};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(data), data,
                          /*skip_stop=*/false));
  return OK_STATUS();
}

static status_t turn_on_leds(void) {
  LOG_INFO("Turning on LEDs via software shutdown bit ...");
  uint8_t ctrl_reg_val = 0;
  TRY(read_led_ctrl_reg(kControlRegAddr, &ctrl_reg_val));
  uint8_t data[2] = {kControlRegAddr, ctrl_reg_val | 0x1};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, /*byte_count=*/sizeof(data), data,
                          /*skip_stop=*/false));
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_init());
  CHECK_STATUS_OK(config_i2c_led_controller());

  CHECK_STATUS_OK(set_led_ctrl_color(kTeacupLedDs5, &kColorBlue));
  CHECK_STATUS_OK(set_led_ctrl_color(kTeacupLedDs9, &kColorRed));
  CHECK_STATUS_OK(set_led_ctrl_color(kTeacupLedDs10, &kColorYellow));
  CHECK_STATUS_OK(set_led_ctrl_color(kTeacupLedDs11, &kColorGreen));

  CHECK_STATUS_OK(turn_on_leds());
  CHECK_STATUS_OK(turn_off_leds());

  return true;
}
