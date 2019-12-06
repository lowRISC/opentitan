// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/boot_rom/bootstrap.h"

#include "sw/device/lib/common.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/gpio.h"
#include "sw/device/lib/hw_sha256.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"  // TODO: Wrap uart in DEBUG macros.
#include "sw/device/lib/oled_driver.h"

extern uint32_t ot_logo[];


// Fills in bit of the progress bar that needs filling for completed frame
// frame_num given total frames frame_total.
//
// Overfills to the left (as it should already have been filled by previous
// frame update) to simplify code.
static void update_oled_progress(uint32_t frame_num, uint32_t frame_total) {
  // Multiply by 256 to handle non-integer cols_per_frame
  uint32_t cols_per_frame = (OLED_BYTE_COLS * 256) / frame_total;
  uint32_t end_cols;

  if (frame_num == frame_total - 1) {
    end_cols = OLED_BYTE_COLS;
  } else {
    end_cols = ((frame_num + 1) * cols_per_frame) / 256;
  }

  // Want to compute word_col aligned byte_col.
  // * >> 8 gives us the byte_col
  // * >> 2 gives us the word_col (combine to get >> 10)
  // * << 2 gives us the byte_col again round down to word_col boundary
  uint32_t start_cols = ((frame_num * cols_per_frame) >> 10) << 2;

  for (uint32_t col = start_cols; col < end_cols; col += 4) {
    uint32_t xor_mask;

    if (col <= (end_cols - 4)) {
      xor_mask = 0xFFFFFFFF;
    } else {
      xor_mask = (1 << ((end_cols - col) * 8)) - 1;
    }

    for (uint32_t row = 0; row < OLED_ROWS; ++row) {
      oled_write_pixbuf_word(row, col >> 2, ot_logo[(col >> 2) + row * OLED_WORD_COLS] ^ xor_mask);
    }
  }

  oled_write_disp();
}

/* Checks if flash is blank to determine if bootstrap is needed. */
/* TODO: Update this to check bootstrap pin instead in Verilator. */
static int bootstrap_requested(void) {
// The following flash empty-sniff-check is done this way due to the lack of
// clear eflash reset in SIM environments.
//#if defined(SIMULATION)
//  return !!(REG32(FLASH_MEM_BASE_ADDR) == 0 ||
//            REG32(FLASH_MEM_BASE_ADDR) == 0xFFFFFFFF);
//#else
//  return !!(gpio_read() & GPIO_BOOTSTRAP_BIT_MASK);
//#endif
  return 1;
}

/* Erase all flash, and verify blank. */
static int erase_flash(void) {
  if (flash_bank_erase(FLASH_BANK_0)) {
    return E_BS_ERASE;
  }
  if (flash_bank_erase(FLASH_BANK_1)) {
    return E_BS_ERASE;
  }
  if (!flash_check_empty()) {
    return E_BS_NOTEMPTY;
  }
  return 0;
}

/* Calculates SHA256 hash of received data and compares it against recieved
 * hash. Returns 0 if both hashes are identical. */
static int check_frame_hash(const frame_t *f) {
  static uint32_t hash[8];
  uint32_t result = 0;
  hw_SHA256_hash((uint8_t *)&f->hdr.frame_num, RAW_BUFFER_SIZE - 32,
                 (uint8_t *)hash);
  for (int i = 0; i < 8; ++i) {
    result |= hash[i] ^ f->hdr.hash[i];
  }
  return result;
}

/* Processes frames received via spid interface and writes them to flash. */
static int bootstrap_flash(void) {
  static frame_t f;
  static uint8_t ack[32] = {0};
  uint32_t expected_frame_no = 0;
  for (;;) {
    if (spid_bytes_available() >= sizeof(f)) {
      spid_read_nb(&f, sizeof(f));
      uint32_t frame_total = (f.hdr.frame_num & 0x7FFF0000) >> 16;

      if (frame_total != 0) {
        update_oled_progress(f.hdr.frame_num & 0xFFFF, frame_total);
      }

      uart_send_str("Processing frame no: ");
      uart_send_uint(f.hdr.frame_num, 32);
      uart_send_str(" exp no: ");
      uart_send_uint(expected_frame_no, 32);
      uart_send_str(" total no: ");
      uart_send_uint(frame_total, 32);
      uart_send_str("\r\n");

      if (FRAME_NO(f.hdr.frame_num) == expected_frame_no) {
        if (check_frame_hash(&f)) {
          uart_send_str("Error: detected hash mismatch on frame: ");
          uart_send_uint(f.hdr.frame_num, 32);
          uart_send_str("\r\n");
          spid_send(ack, sizeof(ack));
          continue;
        }

        hw_SHA256_hash(&f, sizeof(f), ack);
        spid_send(ack, sizeof(ack));

        if (expected_frame_no == 0) {
          flash_default_region_access(/*rd_en=*/1, /*prog_en=*/1,
                                      /*erase_en=*/1);
          int rv = erase_flash();
          if (rv) {
            return rv;
          }
        }
        if (flash_write(f.hdr.flash_offset, f.data, ARRAYSIZE(f.data))) {
          return E_BS_WRITE;
        }

        ++expected_frame_no;
        if (f.hdr.frame_num & FRAME_EOF_MARKER) {
          break;
        }
      } else {
        // Send previous ack if unable to verify current frame.
        spid_send(ack, sizeof(ack));
      }
    }
  }
  uart_send_str("bootstrap: DONE!\r\n");
  return 0;
}

int bootstrap(void) {
  if (!bootstrap_requested()) {
    return 0;
  }
  // SPI device is only initialized in bootstrap mode.
  uart_send_str("Bootstrap requested, initialising HW...\r\n");
  spid_init();
  flash_init_block();

  uart_send_str("HW initialisation completed, waiting for SPI input...\r\n");
  int rv = bootstrap_flash();
  if (rv) {
    rv |= erase_flash();
  }

  // Always make sure to revert flash_ctrl access to default settings.
  // bootstrap_flash enables access to flash to perform update.
  flash_default_region_access(/*rd_en=*/0, /*prog_en=*/0, /*erase_en=*/0);
  return rv;
}
