// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/peripherals/ssd1131_screen.h"

#include "sw/device/examples/teacup_demos/data/bitmaps.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/log.h"

status_t screen_tx_cmd_or_data(const screen_t *screen, uint8_t data,
                               screen_op_type_t op_type) {
  dif_spi_host_segment_t segment = {
      .type = kDifSpiHostSegmentTypeOpcode,
      .opcode = {.width = kDifSpiHostWidthStandard, .opcode = data}};
  TRY(dif_spi_host_wait_until_idle(screen->spi_host));
  TRY(dif_gpio_write(screen->gpio, screen->data_command_gpio, (bool)op_type));
  TRY(dif_spi_host_transaction(screen->spi_host, /*cs_id=*/0, &segment,
                               /*length=*/1));
  TRY(dif_spi_host_wait_until_idle(screen->spi_host));
  return OK_STATUS();
}

status_t screen_toggle_power(const screen_t *screen, bool on) {
  if (on) {
    TRY(screen_tx_cmd_or_data(screen, kScreenSetDisplayOn,
                              kScreenOpTypeCommand));
  } else {
    TRY(screen_tx_cmd_or_data(screen, kScreenSetDisplayOff,
                              kScreenOpTypeCommand));
  }
  return OK_STATUS();
}

status_t screen_toggle_pixel_mode(const screen_t *screen,
                                  screen_pixel_mode_t mode) {
  TRY(screen_tx_cmd_or_data(screen, (uint8_t)mode, kScreenOpTypeCommand));
  return OK_STATUS();
}

status_t screen_set_column_address_range(const screen_t *screen,
                                         uint8_t start_address,
                                         uint8_t end_address) {
  if (start_address >= kScreenMaxCols || end_address >= kScreenMaxCols) {
    return INVALID_ARGUMENT();
  }

  TRY(screen_tx_cmd_or_data(screen, kScreenSetColumnAddress,
                            kScreenOpTypeCommand));
  TRY(screen_tx_cmd_or_data(screen, start_address, kScreenOpTypeCommand));
  TRY(screen_tx_cmd_or_data(screen, end_address, kScreenOpTypeCommand));

  return OK_STATUS();
}

status_t screen_set_row_address_range(const screen_t *screen,
                                      uint8_t start_address,
                                      uint8_t end_address) {
  if (start_address >= kScreenMaxRows || end_address >= kScreenMaxRows) {
    return INVALID_ARGUMENT();
  }

  TRY(screen_tx_cmd_or_data(screen, kScreenSetRowAddress,
                            kScreenOpTypeCommand));
  TRY(screen_tx_cmd_or_data(screen, start_address, kScreenOpTypeCommand));
  TRY(screen_tx_cmd_or_data(screen, end_address, kScreenOpTypeCommand));

  return OK_STATUS();
}

status_t screen_configure_color_format(const screen_t *screen,
                                       screen_color_format_t format) {
  // Set specified color format, in addition to enabling COM split odd/even.
  uint8_t remap_and_color_format_value = (uint8_t)(format << 6 | 0x20);
  TRY(screen_tx_cmd_or_data(screen, kScreenSetRemapAndColorFormat,
                            kScreenOpTypeCommand));
  TRY(screen_tx_cmd_or_data(screen, remap_and_color_format_value,
                            kScreenOpTypeCommand));

  return OK_STATUS();
}

status_t screen_draw_bitmap(const screen_t *screen,
                            const screen_bitmap_t *bitmap) {
  if (bitmap->num_rows > kScreenMaxRows || bitmap->num_cols > kScreenMaxCols) {
    return INVALID_ARGUMENT();
  }

  uint8_t col_start_address = (uint8_t)(kScreenMaxCols - bitmap->num_cols) / 2;
  uint8_t col_end_address = col_start_address + (uint8_t)bitmap->num_cols - 1;
  uint8_t row_start_address = (uint8_t)(kScreenMaxRows - bitmap->num_rows) / 2;
  uint8_t row_end_address = row_start_address + (uint8_t)bitmap->num_rows - 1;

  for (size_t r = 0; r < kScreenMaxRows; ++r) {
    for (size_t c = 0; c < kScreenMaxCols; ++c) {
      uint16_t curr_value = bitmap->fill_color;
      if (c >= col_start_address && c <= col_end_address &&
          r >= row_start_address && r <= row_end_address) {
        size_t adjusted_r = r - row_start_address;
        size_t adjusted_c = c - col_start_address;
        curr_value =
            *(bitmap->bitmap + adjusted_r * bitmap->num_cols + adjusted_c);
      }
      TRY(screen_tx_cmd_or_data(screen, (uint8_t)((curr_value & 0xff00) >> 8),
                                kScreenOpTypeData));
      TRY(screen_tx_cmd_or_data(screen, (uint8_t)(curr_value & 0x00ff),
                                kScreenOpTypeData));
    }
  }

  return OK_STATUS();
}
