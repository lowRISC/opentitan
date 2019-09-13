// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "common.h"
#include "flash_ctrl.h"
#include "gpio.h"
#include "uart.h"

#define DATA_MAX 32

/**
 * Delay loop executing within 8 cycles on ibex
 */
static void delay_loop_ibex(unsigned long loops) {
  int out; /* only to notify compiler of modifications to |loops| */
  asm volatile(
      "1: nop             \n"  // 1 cycle
      "   nop             \n"  // 1 cycle
      "   nop             \n"  // 1 cycle
      "   nop             \n"  // 1 cycle
      "   addi %1, %1, -1 \n"  // 1 cycle
      "   bnez %1, 1b     \n"  // 3 cycles
      : "=&r"(out)
      : "0"(loops));
}

static int usleep_ibex(unsigned long usec) {
  unsigned long usec_cycles;
  usec_cycles = CLK_FIXED_FREQ_HZ * usec / 1000 / 1000 / 8;

  delay_loop_ibex(usec_cycles);
  return 0;
}

static int usleep(unsigned long usec) { return usleep_ibex(usec); }

static void break_on_error(uint32_t error) {
  if (error) {
    // inifinitely fetch instructions, will flag an assertion error
    uart_send_str("Test Failed!\r\n");
    while (1) {
      usleep_ibex(100);
    }
  }

  // otherwise do nothing and continue
}

#define MK_PRINT(c) (((c < 32) || (c > 126)) ? '_' : c)

int main(int argc, char **argv) {
  uart_init(UART_BAUD_RATE);

  // Stupid flash testing
  uint32_t num_words;
  uint32_t i;
  uint32_t prog_array[DATA_MAX];
  uint32_t rd_array[DATA_MAX];
  uint32_t max_size;
  uint32_t start_addr;
  uint32_t data_pat;
  uint32_t flash_bank1_loc = FLASH_MEM_BASE_ADDR + FLASH_BANK_SZ;

  // wait for flash to finish "initializing"
  wait_flash_init();

  // enable all access
  flash_default_region(1, 1, 1);

  // program flash
  num_words = 32;
  for (i = 0; i < num_words; i++) {
    prog_array[i] = i;
  }

  break_on_error(prog_flash(flash_bank1_loc, num_words, prog_array));

  // read flash back
  num_words = 32;
  break_on_error(read_flash(flash_bank1_loc, num_words, rd_array));

  for (i = 0; i < num_words; i++) {
    if (prog_array[i] != rd_array[i]) {
      REG32(FLASH_CTRL_SCRATCH(0)) = rd_array[i];
      break_on_error(1);
    }
  }

  // erase flash and verify
  // The controller auto rounds down to the closest page for page erase
  break_on_error(page_erase(flash_bank1_loc + FLASH_PAGE_SZ - 1));

  REG32(FLASH_CTRL_SCRATCH(0)) = 0xFACEDEAD;

  // read flash back via host to ensure everything is cleared
  for (i = 0; i < 256; i++) {
    if (REG32(flash_bank1_loc + i * 4) != 0xFFFFFFFF) {
      REG32(FLASH_CTRL_SCRATCH(0)) = 0xDEADBEEF;
      break_on_error(1);
    }
  }

  // do 4K programming
  // employ the live programming method where overall payload >> flash fifo size
  max_size = 1024;
  start_addr = flash_bank1_loc + 0x8c68;
  setup_flash_prog(start_addr, max_size);

  for (i = 0; i < max_size; i++) {
    data_pat = (i % 2) ? 0xA5A5A5A5 : 0x5A5A5A5A;
    REG32(FLASH_CTRL_PROG_FIFO(0)) = data_pat + i;
  }

  // wait for operation finish
  wait_done_and_ack();

  // read back 4K programming
  for (i = 0; i < max_size; i++) {
    data_pat = (i % 2) ? 0xA5A5A5A5 : 0x5A5A5A5A;

    if (REG32(start_addr + i * 4) != data_pat + i) {
      REG32(FLASH_CTRL_SCRATCH(0)) = i << 16 | 0xDEAD;
      break_on_error(1);
    }
  }

  /////////////////////////////////////////////////////////////
  // Begin flash memory protection testing
  /////////////////////////////////////////////////////////////

  // turn off default region all access
  flash_default_region(0, 0, 0);

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

  mp_region_t region0 = {
      0,                 // region 0
      region_base_page,  // page 1 of bank1
      region_size,       // size of 1 page
      1,                 // allow read
      1,                 // allow program
      1                  // allow erase
  };
  flash_cfg_region(region0);

  for (uint32_t i = 0; i < good_words + bad_words; i++) {
    prog_array[i] = 0xA5A5A5A5 + i;
  }

  break_on_error(!prog_flash(chk_addr, good_words + bad_words, prog_array));

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
  break_on_error(!page_erase(bad_addr_start));

  // erase the good page
  break_on_error(page_erase(good_addr_start));

  // double check erase results
  for (uint32_t i = 0; i < FLASH_WORDS_PER_PAGE; i++) {
    if (REG32(good_addr_start + i * 4) != 0xFFFFFFFF) {
      break_on_error(1);
    }
  }

  // cleanly terminiate execution
  uart_send_str("Test Passed!\r\n");
  __asm__ volatile("wfi;");
}
