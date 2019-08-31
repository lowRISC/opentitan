// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _FLASH_H_
#define _FLASH_H_

#include <stdint.h>

#include "flash_ctrl_regs.h"

#define FLASH_CTRL0_BASE_ADDR 0x40030000
#define WORDS_PER_PAGE 256
#define ERASE_CHECK_WORDS 16
#define BYTES_PER_WORD 4

typedef enum flash_op {
  FlashRead = 0,
  FlashProg = 1,
  FlashErase = 2
} flash_op_t;

typedef enum erase_type { PageErase = 0, BankErase = 1 } erase_type_t;

typedef struct mp_region {
  uint32_t num;  // which region to program
  uint32_t base;
  uint32_t size;
  uint32_t rd_en;
  uint32_t prog_en;
  uint32_t erase_en;
} mp_region_t;

void wait_flash_init(void);
void wait_done_and_ack(void);
void setup_flash_prog(uint32_t addr, uint32_t num);
uint32_t prog_flash(uint32_t addr, uint32_t num, uint32_t *data);
uint32_t read_flash(uint32_t addr, uint32_t num, uint32_t *data);
uint32_t page_erase(uint32_t addr);
void flash_default_region(uint32_t rd_en, uint32_t prog_en, uint32_t erase_en);
void flash_cfg_region(mp_region_t region_cfg);

#endif
