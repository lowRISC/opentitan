// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/teacup_demos/data/bitmaps.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/boards/teacup_v1_3_0/leds.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/peripherals/ssd1131_screen.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * OT Peripheral Handles.
 */
static dif_i2c_t i2c;
static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
static dif_spi_host_t spi_host;
static screen_t screen;

/**
 * Defined Constants.
 */
enum {
  // Demo Control
  kDemoNumCycles = 50,

  // LED Control
  kLedNumColorsInCycle = 4,
  kLedCyclePauseMilliseconds = 500,
  kLedBrightnessLowPercent = 5,
  kLedBrightnessHighPercent = 40,
  kLedBrightnessStepPercent = 5,

  // Screen Control
  kScreenSpiDataCommandGpio = 1,
  kScreenBitmapsInCycle = 1,
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

/**
 * Pinmux pad attributes for the SPI host pins.
 */
static const pinmux_pad_attributes_t kPinmuxPadAttrs[] = {
    {
        .pad = kTopEarlgreyMuxedPadsIoa2,  // CS
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyMuxedPadsIob7,  // SCK
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyMuxedPadsIob2,  // SD0
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
};

/**
 * Screen bitmaps.
 */
const screen_bitmap_t *kScreenBitmaps[kScreenBitmapsInCycle] = {
    &kOtLogoBitmap,
};

static status_t peripheral_init(void) {
  // Initialize DIFs.
  TRY(dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c));
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  TRY(dif_spi_host_init(mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR),
                        &spi_host));

  // Initialize Screen.
  screen.gpio = &gpio;
  screen.spi_host = &spi_host;
  screen.data_command_gpio = kScreenSpiDataCommandGpio;

  // Initialize pinmux for LED I2C.
  TRY(dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInI2c0Scl,
                              kTopEarlgreyPinmuxInselIob9));
  TRY(dif_pinmux_input_select(&pinmux, kTopEarlgreyPinmuxPeripheralInI2c0Sda,
                              kTopEarlgreyPinmuxInselIob10));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob9,
                               kTopEarlgreyPinmuxOutselI2c0Scl));
  TRY(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob10,
                               kTopEarlgreyPinmuxOutselI2c0Sda));

  // Initialize pinmux for Screen SPI (CS, SCK, data out).
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa2,
                                        kTopEarlgreyPinmuxOutselSpiHost1Csb));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob7,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sck));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob2,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sd0));

  // Initialize pinmux for Screen GPIOs (IOC6 and 9).
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc6,
                                        kTopEarlgreyPinmuxOutselConstantOne));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoc9,
                                        kTopEarlgreyPinmuxOutselGpioGpio1));

  // Pinmux pad configurations.
  pinmux_testutils_configure_pads(&pinmux, kPinmuxPadAttrs,
                                  ARRAYSIZE(kPinmuxPadAttrs));

  return OK_STATUS();
}

static status_t configure_led_i2c_controller(void) {
  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));
  TRY(i2c_testutils_set_speed(&i2c, kDifI2cSpeedFastPlus));
  TRY(leds_i2c_controller_configure(&i2c));
  return OK_STATUS();
}

static status_t configure_screen_spi_controller(void) {
  dif_spi_host_config_t config = {
      .spi_clock = 10000000,
      .peripheral_clock_freq_hz = (uint32_t)kClockFreqPeripheralHz,
      .chip_select =
          {
              .idle = 1,
              .trail = 1,
              .lead = 1,
          },
      .full_cycle = 0,
      .cpha = 0,
      .cpol = 0,
      .tx_watermark = 0,
      .rx_watermark = 0,
  };
  TRY(dif_gpio_write(&gpio, screen.data_command_gpio, false));
  TRY(dif_gpio_output_set_enabled(&gpio, screen.data_command_gpio,
                                  kDifToggleEnabled));
  TRY(dif_spi_host_configure(&spi_host, config));
  TRY(dif_spi_host_output_set_enabled(&spi_host, true));
  return OK_STATUS();
}

static status_t setup_screen(void) {
  TRY(screen_toggle_power(&screen, /*on=*/true));
  TRY(screen_toggle_pixel_mode(&screen, kScreenPixelModeNormal));
  TRY(screen_configure_color_format(&screen, kScreenColorFormat65k2Byte));
  TRY(screen_tx_cmd_or_data(&screen, kScreenDeactivateScrolling,
                            kScreenOpTypeCommand));
  TRY(screen_set_column_address_range(&screen, 0, kScreenMaxCols - 1));
  TRY(screen_set_row_address_range(&screen, 0, kScreenMaxRows - 1));
  return OK_STATUS();
}

bool test_main(void) {
  // Setup OT and peripherals.
  CHECK_STATUS_OK(peripheral_init());
  CHECK_STATUS_OK(configure_led_i2c_controller());
  CHECK_STATUS_OK(configure_screen_spi_controller());
  CHECK_STATUS_OK(setup_screen());
  CHECK_STATUS_OK(leds_turn_all_on(&i2c));

  // LED brightness levels and colors.
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
  for (size_t i = 0; i < kDemoNumCycles; ++i) {
    for (size_t j = 0; j < kLedNumColorsInCycle; ++j) {
      CHECK_STATUS_OK(
          leds_set_color(&i2c, (i + j) % kNumTeacupLeds, kColorCycle[j]));
    }
    CHECK_STATUS_OK(leds_set_all_brightness(&i2c, curr_brightness));
    CHECK_STATUS_OK(
        screen_draw_bitmap(&screen, kScreenBitmaps[i % kScreenBitmapsInCycle]));
    curr_brightness += brightness_step;
    if (curr_brightness >= brightness_end ||
        curr_brightness <= brightness_start) {
      brightness_step *= -1;
    }
    busy_spin_micros(kLedCyclePauseMilliseconds * 1000);
  }

  // Turn screen and LEDs off.
  CHECK_STATUS_OK(screen_toggle_power(&screen, /*on=*/false));
  CHECK_STATUS_OK(leds_turn_all_off(&i2c));

  return true;
}
