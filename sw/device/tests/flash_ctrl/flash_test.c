// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/gpio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/uart.h"

static void break_on_error(uint32_t error) {
  if (error) {
    // inifinitely fetch instructions, will flag an assertion error
    uart_send_str("FAIL!\r\n");
    while (1) {
      busy_sleep_micros(100);
    }
  }
}

/* Returns 1 if |a| and |b| are equal. */
int check_arr_eq(const uint32_t *a, const uint32_t *b, uint32_t len) {
  for (int i = 0; i < len; ++i) {
    if (a[i] != b[i]) {
      return 0;
    }
  }
  return 1;
}

int main(int argc, char **argv) {
  uint32_t i, iteration;
  uint32_t prog_array[FLASH_WORDS_PER_PAGE];
  uint32_t rd_array[FLASH_WORDS_PER_PAGE];
  uint32_t test_addr;
  uint32_t bank1_addr = FLASH_MEM_BASE_ADDR + FLASH_BANK_SZ;
  uint32_t bank0_last_page =
      FLASH_MEM_BASE_ADDR + (FLASH_PAGES_PER_BANK - 1) * FLASH_PAGE_SZ;

  uart_init(UART_BAUD_RATE);
  flash_init_block();

  // enable all access
  flash_cfg_bank_erase(FLASH_BANK_0, /*erase_en=*/true);
  flash_cfg_bank_erase(FLASH_BANK_1, /*erase_en=*/true);
  flash_default_region_access(1, 1, 1);
  break_on_error(flash_page_erase(bank1_addr));
  flash_write_scratch_reg(0xFACEDEAD);
  // read flash back via host to ensure everything is cleared
  for (i = 0; i < FLASH_WORDS_PER_PAGE; i++) {
    if (REG32(bank1_addr + i * 4) != 0xFFFFFFFF) {
      flash_write_scratch_reg(0xDEADBEEF);
      break_on_error(1);
    }
  }

  // do 4K programming
  // employ the live programming method where overall payload >> flash fifo size
  for (i = 0; i < ARRAYSIZE(prog_array); i++) {
    prog_array[i] = (i % 2) ? 0xA5A5A5A5 : 0x5A5A5A5A;
  }

  // initialize test regions
  break_on_error(flash_page_erase(bank1_addr));
  break_on_error(flash_page_erase(bank0_last_page));
  for (iteration = 0; iteration < 2; iteration++) {
    test_addr = iteration ? bank1_addr : bank0_last_page;
    break_on_error(flash_write(test_addr, prog_array, ARRAYSIZE(prog_array)));
    break_on_error(flash_read(test_addr, ARRAYSIZE(rd_array), rd_array));
    break_on_error(!check_arr_eq(rd_array, prog_array, ARRAYSIZE(rd_array)));
  }

  /////////////////////////////////////////////////////////////
  // Begin flash memory protection testing
  /////////////////////////////////////////////////////////////
  uint32_t region_base_page = FLASH_PAGES_PER_BANK;
  uint32_t region_size = 1;
  uint32_t good_addr_start =
      FLASH_MEM_BASE_ADDR + region_base_page * FLASH_PAGE_SZ;
  uint32_t good_addr_end = good_addr_start + region_size * FLASH_PAGE_SZ - 1;
  uint32_t bad_addr_start =
      good_addr_end + 1;  // this is always aligned to a page
  uint32_t good_words = 3;
  uint32_t bad_words = 3;
  uint32_t chk_addr = bad_addr_start - (FLASH_WORD_SZ * good_words);

  mp_region_t region0 = {.num = 0,
                         .base = region_base_page,
                         .size = region_size,
                         .rd_en = 1,
                         .prog_en = 1,
                         .erase_en = 1};

  // initialize good and bad regions.
  break_on_error(flash_page_erase(good_addr_start));
  break_on_error(flash_page_erase(bad_addr_start));

  // turn off default region all access
  flash_default_region_access(0, 0, 0);
  flash_cfg_region(&region0);

  // expect write to fail.
  for (uint32_t i = 0; i < good_words + bad_words; i++) {
    prog_array[i] = 0xA5A5A5A5 + i;
  }
  break_on_error(!flash_write(chk_addr, prog_array, good_words + bad_words));

  // the good words should match
  for (uint32_t i = 0; i < good_words; i++) {
    if (REG32(chk_addr + i * 4) != prog_array[i]) {
      break_on_error(1);
    }
  }

  // the bad word contents should not have gone through
  for (uint32_t i = good_words; i < good_words + bad_words; i++) {
    if (REG32(chk_addr + i * 4) != 0xFFFFFFFF) {
      break_on_error(1);
    }
  }

  // attempt to erase bad page, should error
  break_on_error(!flash_page_erase(bad_addr_start));

  // erase the good page
  break_on_error(flash_page_erase(good_addr_start));

  // double check erase results
  for (uint32_t i = 0; i < FLASH_WORDS_PER_PAGE; i++) {
    if (REG32(good_addr_start + i * 4) != 0xFFFFFFFF) {
      break_on_error(1);
    }
  }

  flash_cfg_bank_erase(FLASH_BANK_0, /*erase_en=*/false);
  flash_cfg_bank_erase(FLASH_BANK_1, /*erase_en=*/false);

  // cleanly terminate execution
  uart_send_str("PASS!\r\n");
}
