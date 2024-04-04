// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_PERIPHERALS_SSD1131_SCREEN_H_
#define OPENTITAN_SW_DEVICE_LIB_PERIPHERALS_SSD1131_SCREEN_H_

#include "sw/device/examples/teacup_demos/data/bitmaps.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_host.h"

/**
 * Defined Constants.
 */
enum {
  // Max screen sizes.
  kScreenMaxRows = 64,
  kScreenMaxCols = 96,

  // Colors.
  kScreenPixelColorWhite = 0xFFFF,
  kScreenPixelColorBlack = 0x0,
};

/**
 * Screen Handle.
 */
typedef struct screen {
  /**
   * GPIO handle to manipulate the data/command line.
   */
  dif_gpio_t *gpio;
  /**
   * SPI Host handle to send commands / data to the screen.
   */
  dif_spi_host_t *spi_host;
  /**
   * Data/Command control GPIO pin.
   */
  dif_gpio_pin_t data_command_gpio;
} screen_t;

/**
 * Screen operation type.
 */
typedef enum screen_op_type {
  kScreenOpTypeCommand = 0,
  kScreenOpTypeData = 1,
} screen_op_type_t;

/**
 * Screen Commands.
 */
typedef enum screen_commands {
  // Toggle screen on and off.
  kScreenSetDisplayOn = 0xAF,
  kScreenSetDisplayOnDim = 0xAC,
  kScreenSetDisplayOff = 0xAE,

  // Display modes.
  kScreenAllPixelsNormal = 0xA4,
  kScreenAllPixelsOn = 0xA5,
  kScreenAllPixelsOff = 0xA6,
  kScreenAllPixelsInverse = 0xA7,

  // Set column/row addresses.
  kScreenSetColumnAddress = 0x15,
  kScreenSetRowAddress = 0x75,

  // Set remap/color format.
  kScreenSetRemapAndColorFormat = 0xA0,

  // Deactivate scrolling.
  kScreenDeactivateScrolling = 0x2E,
} screen_commands_t;

/**
 * Screen pixel modes.
 */
typedef enum screen_pixel_mode {
  kScreenPixelModeNormal = kScreenAllPixelsNormal,
  kScreenPixelModeAllOn = kScreenAllPixelsOn,
  kScreenPixelModeAllOff = kScreenAllPixelsOff,
  kScreenPixelModeInverse = kScreenAllPixelsInverse,
} screen_pixel_mode_t;

/**
 * Screen color formats.
 */
typedef enum screen_color_format {
  kScreenColorFormat256 = 0,
  kScreenColorFormat65k2Byte = 1,
  kScreenColorFormat65k3Byte = 2,
} screen_color_format_t;

/**
 * Transmits a command or data to the screen.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param data The command or data to send to the screen controller.
 * @param op_type The transaction operation type (command or data).
 */
OT_WARN_UNUSED_RESULT
status_t screen_tx_cmd_or_data(const screen_t *screen, uint8_t data,
                               screen_op_type_t op_type);

/**
 * Toggles the screen power on or off.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param on Whether to turn the screen on or off.
 */
OT_WARN_UNUSED_RESULT status_t screen_toggle_power(const screen_t *screen,
                                                   bool on);

/**
 * Toggles the screen pixel mode.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param mode The pixel mode to set (all on, all off, inverse, or normal).
 */
OT_WARN_UNUSED_RESULT
status_t screen_toggle_pixel_mode(const screen_t *screen,
                                  screen_pixel_mode_t mode);

/**
 * Configures the color format for the screen.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param format Color format for the pixel data.
 */
OT_WARN_UNUSED_RESULT
status_t screen_configure_color_format(const screen_t *screen,
                                       screen_color_format_t format);

/**
 * Set the screen column address range.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param start_address Start column address of the screen RAM array.
 * @param end_address End column address of the screen RAM array.
 */
OT_WARN_UNUSED_RESULT
status_t screen_set_column_address_range(const screen_t *screen,
                                         uint8_t start_address,
                                         uint8_t end_address);

/**
 * Set the screen row address range.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param start_address Start row address of the screen RAM array.
 * @param end_address End row address of the screen RAM array.
 */
OT_WARN_UNUSED_RESULT
status_t screen_set_row_address_range(const screen_t *screen,
                                      uint8_t start_address,
                                      uint8_t end_address);

/**
 * Draw a bitmap on the screen.
 *
 * @param screen Screen handle to communicate with the screen controller.
 * @param bitmap Bitmap to draw on the screen.
 */
OT_WARN_UNUSED_RESULT
status_t screen_draw_bitmap(const screen_t *screen,
                            const screen_bitmap_t *bitmap);

#endif  // OPENTITAN_SW_DEVICE_LIB_PERIPHERALS_SSD1131_SCREEN_H_
