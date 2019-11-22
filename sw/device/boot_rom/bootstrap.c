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

/* Checks if flash is blank to determine if bootstrap is needed. */
/* TODO: Update this to check bootstrap pin instead in Verilator. */
static int bootstrap_requested(void) {
// The following flash empty-sniff-check is done this way due to the lack of
// clear eflash reset in SIM environments.
#if defined(SIMULATION)
  return !!(REG32(FLASH_MEM_BASE_ADDR) == 0 ||
            REG32(FLASH_MEM_BASE_ADDR) == 0xFFFFFFFF);
#else
  return !!(gpio_read() & GPIO_BOOTSTRAP_BIT_MASK);
#endif
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
      uart_send_str("Processing frame no: ");
      uart_send_uint(f.hdr.frame_num, 32);
      uart_send_str(" exp no: ");
      uart_send_uint(expected_frame_no, 32);
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
  uart_send_str("Bootstrap requested, initialising HW...\n");
  spid_init();
  flash_init_block();

  uart_send_str("HW initialisation completed, waiting for SPI input...\n");
  int rv = bootstrap_flash();
  if (rv) {
    rv |= erase_flash();
  }

  // Always make sure to revert flash_ctrl access to default settings.
  // bootstrap_flash enables access to flash to perform update.
  flash_default_region_access(/*rd_en=*/0, /*prog_en=*/0, /*erase_en=*/0);
  return rv;
}
