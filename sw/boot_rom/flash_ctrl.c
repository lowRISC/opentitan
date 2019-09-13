// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "flash_ctrl.h"

#include "common.h"
#include "flash_ctrl_regs.h"

#define FLASH_CTRL0_BASE_ADDR 0x40030000

typedef enum flash_op {
  FlashRead = 0,
  FlashProg = 1,
  FlashErase = 2
} flash_op_t;

typedef enum erase_type { PageErase = 0, BankErase = 1 } erase_type_t;

/* Wait for flash command to complete and set ACK in controller */
static inline void wait_done_and_ack(void) {
  while ((REG32(FLASH_CTRL_OP_STATUS(0)) & (1 << FLASH_CTRL_OP_STATUS_DONE)) ==
         0) {
  };
  REG32(FLASH_CTRL_OP_STATUS(0)) = 0;
}

void flash_init_block(void) {
  while ((REG32(FLASH_CTRL_STATUS(0)) & (1 << FLASH_CTRL_STATUS_INIT_WIP)) >
         0) {
  }
}

int flash_check_empty(void) {
  uint32_t mask = -1u;
  uint32_t *p = (uint32_t *)FLASH_MEM_BASE_ADDR;
  // TODO: Update range to cover entire flash. Limited now to one bank while
  // we debu initialization.
  for (; p < (uint32_t *)(FLASH_MEM_BASE_ADDR + FLASH_BANK_SZ);) {
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    if (mask != -1u) {
      return 0;
    }
  }
  return 1;
}

int flash_bank_erase(bank_index_t idx) {
  REG32(FLASH_CTRL_MP_BANK_CFG(0)) =
      0x1 << ((idx == FlashBank0) ? FLASH_CTRL_MP_BANK_CFG_ERASE_EN0
                                  : FLASH_CTRL_MP_BANK_CFG_ERASE_EN1);

  // TODO: Add timeout conditions and add error codes.
  REG32(FLASH_CTRL_ADDR(0)) = (idx == FlashBank0)
                                  ? FLASH_MEM_BASE_ADDR
                                  : (FLASH_MEM_BASE_ADDR + FLASH_BANK_SZ);
  REG32(FLASH_CTRL_CONTROL(0)) = (FlashErase << FLASH_CTRL_CONTROL_OP_OFFSET |
                                  BankErase << FLASH_CTRL_CONTROL_ERASE_SEL |
                                  0x1 << FLASH_CTRL_CONTROL_START);
  wait_done_and_ack();

  REG32(FLASH_CTRL_MP_BANK_CFG(0)) =
      0x0 << ((idx == FlashBank0) ? FLASH_CTRL_MP_BANK_CFG_ERASE_EN0
                                  : FLASH_CTRL_MP_BANK_CFG_ERASE_EN1);
  return 0;
}

static int flash_write_internal(uint32_t addr, const uint32_t *data,
                                uint32_t size) {
  // TODO: Do we need to select bank as part of the write?
  // TODO: Update with address alignment requirements.
  REG32(FLASH_CTRL_ADDR(0)) = addr;
  REG32(FLASH_CTRL_CONTROL(0)) = (FlashProg << FLASH_CTRL_CONTROL_OP_OFFSET |
                                  (size - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
                                  0x1 << FLASH_CTRL_CONTROL_START);
  for (int i = 0; i < size; ++i) {
    REG32(FLASH_CTRL_PROG_FIFO(0)) = data[i];
  }
  wait_done_and_ack();
  return 0;
}

int flash_write(uint32_t addr, const uint32_t *data, uint32_t size) {
  // TODO: Breakdown into FIFO chunks if needed.
  return flash_write_internal(addr, data, size);
}

void flash_default_region_access(bool rd_en, bool prog_en, bool erase_en) {
  REG32(FLASH_CTRL_DEFAULT_REGION(0)) =
      rd_en << FLASH_CTRL_DEFAULT_REGION_RD_EN |
      prog_en << FLASH_CTRL_DEFAULT_REGION_PROG_EN |
      erase_en << FLASH_CTRL_DEFAULT_REGION_ERASE_EN;
}
