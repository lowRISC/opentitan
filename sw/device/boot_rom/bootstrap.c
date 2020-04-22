// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/boot_rom/bootstrap.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/hw_sha256.h"
#include "sw/device/lib/spi_device.h"
#include "sw/device/lib/uart.h"  // TODO: Wrap uart in DEBUG macros.

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define GPIO_BOOTSTRAP_BIT_MASK 0x00020000u

/* Checks if flash is blank to determine if bootstrap is needed. */
/* TODO: Update this to check bootstrap pin instead in Verilator. */
static int bootstrap_requested(void) {
  // The following flash empty-sniff-check is done this way due to the lack of
  // clear eflash reset in SIM environments.
  if (kDeviceType == kDeviceSimVerilator) {
    return !!(REG32(FLASH_MEM_BASE_ADDR) == 0 ||
              REG32(FLASH_MEM_BASE_ADDR) == 0xFFFFFFFF);
  }
  // Initialize GPIO device
  dif_gpio_t gpio;
  dif_gpio_config_t gpio_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR)};
  dif_gpio_init(&gpio_config, &gpio);
  // Read pin
  uint32_t gpio_in;
  dif_gpio_all_read(&gpio, &gpio_in);
  return !!(gpio_in & GPIO_BOOTSTRAP_BIT_MASK);
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
      LOG_INFO("Processing frame no: %d exp no: %d", f.hdr.frame_num,
               expected_frame_no);

      if (FRAME_NO(f.hdr.frame_num) == expected_frame_no) {
        if (check_frame_hash(&f)) {
          LOG_ERROR("Detected hash mismatch on frame: %d", f.hdr.frame_num);
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
  LOG_INFO("bootstrap: DONE!");
  return 0;
}

int bootstrap(void) {
  if (!bootstrap_requested()) {
    return 0;
  }
  // SPI device is only initialized in bootstrap mode.
  LOG_INFO("Bootstrap requested, initialising HW...");
  spid_init();
  flash_init_block();

  LOG_INFO("HW initialisation completed, waiting for SPI input...");
  int rv = bootstrap_flash();
  if (rv) {
    rv |= erase_flash();
  }

  // Always make sure to revert flash_ctrl access to default settings.
  // bootstrap_flash enables access to flash to perform update.
  flash_default_region_access(/*rd_en=*/0, /*prog_en=*/0, /*erase_en=*/0);
  return rv;
}
