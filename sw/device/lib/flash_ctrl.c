// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/flash_ctrl.h"

#include "flash_ctrl_regs.h"  // Generated.

#include "sw/device/lib/common.h"

#define FLASH_CTRL0_BASE_ADDR 0x40030000

typedef enum flash_op {
  FLASH_READ = 0,
  FLASH_PROG = 1,
  FLASH_ERASE = 2
} flash_op_t;

typedef enum erase_type {
  FLASH_PAGE_ERASE = 0,
  FLASH_BANK_ERASE = 1
} erase_type_t;

/* Wait for flash command to complete and set ACK in controller */
static inline void wait_done_and_ack(void) {
  while ((REG32(FLASH_CTRL_OP_STATUS(0)) & (1 << FLASH_CTRL_OP_STATUS_DONE)) ==
         0) {
  }
  REG32(FLASH_CTRL_OP_STATUS(0)) = 0;
}

void flash_init_block(void) {
  while ((REG32(FLASH_CTRL_STATUS(0)) & (1 << FLASH_CTRL_STATUS_INIT_WIP)) >
         0) {
  }
}

/* Return status error and clear internal status register */
static int get_clr_err(void) {
  uint32_t err_status =
      REG32(FLASH_CTRL_INTR_STATE(0)) & (0x1 << FLASH_CTRL_INTR_STATE_OP_ERROR);
  REG32(FLASH_CTRL_INTR_STATE(0)) = err_status;
  return err_status;
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
  flash_cfg_bank_erase(idx, /*erase_en=*/true);

  // TODO: Add timeout conditions and add error codes.
  REG32(FLASH_CTRL_ADDR(0)) = (idx == FLASH_BANK_0)
                                  ? FLASH_MEM_BASE_ADDR
                                  : (FLASH_MEM_BASE_ADDR + FLASH_BANK_SZ);
  REG32(FLASH_CTRL_CONTROL(0)) =
      (FLASH_ERASE << FLASH_CTRL_CONTROL_OP_OFFSET |
       FLASH_BANK_ERASE << FLASH_CTRL_CONTROL_ERASE_SEL |
       0x1 << FLASH_CTRL_CONTROL_START);
  wait_done_and_ack();

  flash_cfg_bank_erase(idx, /*erase_en=*/false);

  return get_clr_err();
}

int flash_page_erase(uint32_t addr) {
  REG32(FLASH_CTRL_ADDR(0)) = addr;
  REG32(FLASH_CTRL_CONTROL(0)) = FLASH_ERASE << FLASH_CTRL_CONTROL_OP_OFFSET |
                                 FLASH_PAGE_ERASE
                                     << FLASH_CTRL_CONTROL_ERASE_SEL |
                                 0x1 << FLASH_CTRL_CONTROL_START;
  wait_done_and_ack();
  return get_clr_err();
}

static int flash_write_internal(uint32_t addr, const uint32_t *data,
                                uint32_t size) {
  // TODO: Do we need to select bank as part of the write?
  // TODO: Update with address alignment requirements.
  REG32(FLASH_CTRL_ADDR(0)) = addr;
  REG32(FLASH_CTRL_CONTROL(0)) = (FLASH_PROG << FLASH_CTRL_CONTROL_OP_OFFSET |
                                  (size - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
                                  0x1 << FLASH_CTRL_CONTROL_START);
  for (int i = 0; i < size; ++i) {
    REG32(FLASH_CTRL_PROG_FIFO(0)) = data[i];
  }
  wait_done_and_ack();
  return get_clr_err();
}

int flash_write(uint32_t addr, const uint32_t *data, uint32_t size) {
  // TODO: Breakdown into FIFO chunks if needed.
  return flash_write_internal(addr, data, size);
}

int flash_read(uint32_t addr, uint32_t size, uint32_t *data) {
  REG32(FLASH_CTRL_ADDR(0)) = addr;
  REG32(FLASH_CTRL_CONTROL(0)) = FLASH_READ << FLASH_CTRL_CONTROL_OP_OFFSET |
                                 (size - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
                                 0x1 << FLASH_CTRL_CONTROL_START;
  for (uint32_t i = 0; i < size;) {
    if (((REG32(FLASH_CTRL_STATUS(0)) >> FLASH_CTRL_STATUS_RD_EMPTY) & 0x1) ==
        0) {
      *data++ = REG32(FLASH_CTRL_RD_FIFO(0));
      i++;
    }
  }
  wait_done_and_ack();
  return get_clr_err();
}

void flash_cfg_bank_erase(bank_index_t bank, bool erase_en) {
  REG32(FLASH_CTRL_MP_BANK_CFG(0)) =
      (erase_en) ? SETBIT(REG32(FLASH_CTRL_MP_BANK_CFG(0)), bank)
                 : CLRBIT(REG32(FLASH_CTRL_MP_BANK_CFG(0)), bank);
}

void flash_default_region_access(bool rd_en, bool prog_en, bool erase_en) {
  REG32(FLASH_CTRL_DEFAULT_REGION(0)) =
      rd_en << FLASH_CTRL_DEFAULT_REGION_RD_EN |
      prog_en << FLASH_CTRL_DEFAULT_REGION_PROG_EN |
      erase_en << FLASH_CTRL_DEFAULT_REGION_ERASE_EN;
}

void flash_cfg_region(const mp_region_t *region_cfg) {
  REG32(FLASH_CTRL_MP_REGION_CFG0(0) + region_cfg->num * 4) =
      region_cfg->base << FLASH_CTRL_MP_REGION_CFG0_BASE0_OFFSET |
      region_cfg->size << FLASH_CTRL_MP_REGION_CFG0_SIZE0_OFFSET |
      region_cfg->rd_en << FLASH_CTRL_MP_REGION_CFG0_RD_EN0 |
      region_cfg->prog_en << FLASH_CTRL_MP_REGION_CFG0_PROG_EN0 |
      region_cfg->erase_en << FLASH_CTRL_MP_REGION_CFG0_ERASE_EN0 |
      0x1 << FLASH_CTRL_MP_REGION_CFG0_EN0;
}

void flash_write_scratch_reg(uint32_t value) {
  REG32(FLASH_CTRL_SCRATCH(0)) = value;
}

uint32_t flash_read_scratch_reg(void) { return REG32(FLASH_CTRL_SCRATCH(0)); }
