// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "bootstrap.h"

#include "common.h"
#include "flash_ctrl.h"
#include "gpio.h"
#include "spi_device.h"
#include "uart.h"  // TODO: Wrap uart in DEBUG macros.

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

      // TODO: Add hash check.
      if (FRAME_NO(f.hdr.frame_num) == expected_frame_no) {
        // TODO: Add ack computation.
        spid_send(ack, sizeof(ack));

        if (expected_frame_no == 0) {
          // TODO: Add signed header checks.
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
  spid_init();
  flash_init_block();

  int rv = bootstrap_flash();

  // Always make sure to revert flash_ctrl access to default settings.
  // bootstrap_flash enables access to flash to perform update.
  flash_default_region_access(/*rd_en=*/0, /*prog_en=*/0, /*erase_en=*/0);
  return rv;
}
