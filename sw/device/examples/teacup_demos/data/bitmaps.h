// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_EXAMPLES_TEACUP_DEMOS_DATA_BITMAPS_H_
#define OPENTITAN_SW_DEVICE_EXAMPLES_TEACUP_DEMOS_DATA_BITMAPS_H_

#include <stddef.h>
#include <stdint.h>

/**
 * A bitmap to draw on a screen.
 */
typedef struct screen_bitmap {
  /**
   * Number of rows in the bitmap.
   */
  const size_t num_rows;
  /**
   * Number of columns in the bitmap.
   */
  const size_t num_cols;
  /**
   * A 2D bitmap array.
   */
  const uint16_t *bitmap;
  /**
   * Fill color to surround image by.
   */
  const uint16_t fill_color;
} screen_bitmap_t;

/**
 * Example bitmap(s).
 */
extern const screen_bitmap_t kOtLogoBitmap;

#endif  // OPENTITAN_SW_DEVICE_EXAMPLES_TEACUP_DEMOS_DATA_BITMAPS_H_
