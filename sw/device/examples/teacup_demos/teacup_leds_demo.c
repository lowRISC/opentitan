// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/boards/teacup_v1_3_0/leds.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/hart.h"
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
 * Defined Constants.
 */
enum {
  kLedNumCycles = 100,
  kLedNumColorsInCycle = 4,
  kLedCyclePauseMilliseconds = 200,
  kLedBrightnessLowPercent = 5,
  kLedBrightnessHighPercent = 40,
  kLedBrightnessStepPercent = 5,
};

static const led_rgb_color_t kLedColorBlue = {
    .r = 0x33,
    .g = 0x69,
    .b = 0xE8,
};

static const led_rgb_color_t kLedColorRed = {
    .r = 0xD5,
    .g = 0x0F,
    .b = 0x25,
};

static const led_rgb_color_t kLedColorYellow = {
    .r = 0xEE,
    .g = 0xB2,
    .b = 0x11,
};

static const led_rgb_color_t kLedColorGreen = {
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

static status_t configure_led_i2c_controller(void) {
  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));
  TRY(i2c_testutils_set_speed(&i2c, kDifI2cSpeedFastPlus));
  TRY(leds_i2c_controller_configure(&i2c));
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_init());
  CHECK_STATUS_OK(configure_led_i2c_controller());
  CHECK_STATUS_OK(leds_turn_all_on(&i2c));

  // Brightness levels and colors.
  uint8_t brightness_start =
      (uint8_t)((float)0xFF * (float)kLedBrightnessLowPercent / 100.0);
  uint8_t brightness_end =
      (uint8_t)((float)0xFF * (float)kLedBrightnessHighPercent / 100.0);
  uint8_t brightness_step =
      (uint8_t)((float)0xFF * (float)kLedBrightnessStepPercent / 100.0);
  uint8_t curr_brightness = brightness_start;
  const led_rgb_color_t kColorCycle[kLedNumColorsInCycle] = {
      kLedColorBlue,
      kLedColorRed,
      kLedColorYellow,
      kLedColorGreen,
  };

  // Cycle through brightness levels and colors.
  for (size_t i = 0; i < kLedNumCycles; ++i) {
    for (size_t j = 0; j < kLedNumColorsInCycle; ++j) {
      CHECK_STATUS_OK(
          leds_set_color(&i2c, (i + j) % kNumTeacupLeds, kColorCycle[j]));
    }
    CHECK_STATUS_OK(leds_set_all_brightness(&i2c, curr_brightness));
    curr_brightness += brightness_step;
    if (curr_brightness >= brightness_end ||
        curr_brightness <= brightness_start) {
      brightness_step *= -1;
    }
    busy_spin_micros(kLedCyclePauseMilliseconds * 1000);
  }

  CHECK_STATUS_OK(leds_turn_all_off(&i2c));

  return true;
}
