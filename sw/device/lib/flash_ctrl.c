// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/flash_ctrl.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define FLASH_CTRL0_BASE_ADDR TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR

#define PROGRAM_RESOLUTION_WORDS \
  (FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES / sizeof(uint32_t))

#define REG32(add) *((volatile uint32_t *)(add))
#define SETBIT(val, bit) (val | 1 << bit)
#define CLRBIT(val, bit) (val & ~(1 << bit))

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
  mmio_region_t flash_ctrl_base =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);

  while ((mmio_region_read32(flash_ctrl_base, FLASH_CTRL_OP_STATUS_REG_OFFSET) &
          (1 << FLASH_CTRL_OP_STATUS_DONE_BIT)) == 0) {
  }
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_OP_STATUS_REG_OFFSET) = 0;
}

void flash_init_block(void) {
  mmio_region_t flash_ctrl_base =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);

  while ((mmio_region_read32(flash_ctrl_base, FLASH_CTRL_STATUS_REG_OFFSET) &
          (1 << FLASH_CTRL_STATUS_INIT_WIP_BIT)) > 0) {
  }
}

/* Return status error and clear internal status register */
static int get_clr_err(void) {
  uint32_t err_status =
      REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_ERR_CODE_REG_OFFSET);
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_ERR_CODE_REG_OFFSET) = -1u;
  return err_status;
}

int flash_check_empty(void) {
  uint32_t mask = -1u;
  uint32_t *p = (uint32_t *)FLASH_MEM_BASE_ADDR;
  // TODO: Update range to cover entire flash. Limited now to one bank while
  // we debu initialization.
  for (; p < (uint32_t *)(FLASH_MEM_BASE_ADDR + flash_get_bank_size());) {
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
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_ADDR_REG_OFFSET) =
      (idx == FLASH_BANK_0) ? FLASH_MEM_BASE_ADDR
                            : (FLASH_MEM_BASE_ADDR + flash_get_bank_size());
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_CONTROL_REG_OFFSET) =
      (FLASH_ERASE << FLASH_CTRL_CONTROL_OP_OFFSET |
       FLASH_BANK_ERASE << FLASH_CTRL_CONTROL_ERASE_SEL_BIT |
       0x1 << FLASH_CTRL_CONTROL_START_BIT);
  wait_done_and_ack();

  flash_cfg_bank_erase(idx, /*erase_en=*/false);

  return get_clr_err();
}

int flash_page_erase(uint32_t addr, part_type_t part) {
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_ADDR_REG_OFFSET) = addr;
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_CONTROL_REG_OFFSET) =
      FLASH_ERASE << FLASH_CTRL_CONTROL_OP_OFFSET |
      FLASH_PAGE_ERASE << FLASH_CTRL_CONTROL_ERASE_SEL_BIT |
      part << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
      0x1 << FLASH_CTRL_CONTROL_START_BIT;
  wait_done_and_ack();
  return get_clr_err();
}

static int flash_write_internal(uint32_t addr, part_type_t part,
                                const uint32_t *data, uint32_t size) {
  // TODO: Do we need to select bank as part of the write?
  // TODO: Update with address alignment requirements.
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_ADDR_REG_OFFSET) = addr;
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_CONTROL_REG_OFFSET) =
      (FLASH_PROG << FLASH_CTRL_CONTROL_OP_OFFSET |
       part << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
       (size - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
       0x1 << FLASH_CTRL_CONTROL_START_BIT);
  for (int i = 0; i < size; ++i) {
    REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_PROG_FIFO_REG_OFFSET) = data[i];
  }
  wait_done_and_ack();
  return get_clr_err();
}

// The address is assumed to be aligned to uint32_t.
int flash_write(uint32_t addr, part_type_t part, const uint32_t *data,
                uint32_t size) {
  uint32_t window_offset = (addr / sizeof(uint32_t)) % PROGRAM_RESOLUTION_WORDS;
  uint32_t max_words = PROGRAM_RESOLUTION_WORDS;

  // If initial address isn't aligned, the delta is the max
  // number of words that can be programmed.
  max_words = PROGRAM_RESOLUTION_WORDS - window_offset;

  // Loop through the amount of data to program.
  uint32_t words_to_program = max_words;
  uint32_t words_remaining = size;
  uint32_t current_word = 0;
  uint32_t err = 0;
  while (words_remaining > 0) {
    // Determine the number of words to program.
    if (words_remaining < max_words) {
      words_to_program = words_remaining;
    } else {
      words_to_program = max_words;
    }
    err |= flash_write_internal(addr + current_word * sizeof(uint32_t), part,
                                data, words_to_program);
    current_word += words_to_program;
    data += words_to_program;

    // Increment remaining words and reset max words to program.
    max_words = PROGRAM_RESOLUTION_WORDS;
    words_remaining = size - current_word;
  }
  return err;
}

int flash_read(uint32_t addr, part_type_t part, uint32_t size, uint32_t *data) {
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_ADDR_REG_OFFSET) = addr;
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_CONTROL_REG_OFFSET) =
      FLASH_READ << FLASH_CTRL_CONTROL_OP_OFFSET |
      part << FLASH_CTRL_CONTROL_PARTITION_SEL_BIT |
      (size - 1) << FLASH_CTRL_CONTROL_NUM_OFFSET |
      0x1 << FLASH_CTRL_CONTROL_START_BIT;
  for (uint32_t i = 0; i < size;) {
    if (((REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_STATUS_REG_OFFSET) >>
          FLASH_CTRL_STATUS_RD_EMPTY_BIT) &
         0x1) == 0) {
      *data++ = REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_RD_FIFO_REG_OFFSET);
      i++;
    }
  }
  wait_done_and_ack();
  return get_clr_err();
}

void flash_cfg_bank_erase(bank_index_t bank, bool erase_en) {
  mmio_region_t flash_ctrl_base =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);

  uint32_t val =
      (erase_en)
          ? SETBIT(
                mmio_region_read32(flash_ctrl_base,
                                   FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET),
                bank)
          : CLRBIT(
                mmio_region_read32(flash_ctrl_base,
                                   FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET),
                bank);

  mmio_region_write32_shadowed(flash_ctrl_base,
                               FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET, val);
}

void flash_default_region_access(bool rd_en, bool prog_en, bool erase_en) {
  mmio_region_t flash_ctrl_base =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);

  uint32_t reg = 0;
  reg =
      bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_RD_EN_FIELD,
                             rd_en ? kMultiBitBool4True : kMultiBitBool4False);
  reg = bitfield_field32_write(
      reg, FLASH_CTRL_DEFAULT_REGION_PROG_EN_FIELD,
      prog_en ? kMultiBitBool4True : kMultiBitBool4False);
  reg = bitfield_field32_write(
      reg, FLASH_CTRL_DEFAULT_REGION_ERASE_EN_FIELD,
      erase_en ? kMultiBitBool4True : kMultiBitBool4False);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD,
                               kMultiBitBool4False);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_ECC_EN_FIELD,
                               kMultiBitBool4False);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_HE_EN_FIELD,
                               kMultiBitBool4False);

  mmio_region_write32(flash_ctrl_base, FLASH_CTRL_DEFAULT_REGION_REG_OFFSET,
                      reg);
}

uint32_t flash_get_banks(void) { return FLASH_CTRL_PARAM_REG_NUM_BANKS; }

uint32_t flash_get_pages_per_bank(void) {
  return FLASH_CTRL_PARAM_REG_PAGES_PER_BANK;
}

uint32_t flash_get_words_per_page(void) {
  return FLASH_CTRL_PARAM_WORDS_PER_PAGE;
}

uint32_t flash_get_bank_size(void) { return FLASH_CTRL_PARAM_BYTES_PER_BANK; }

uint32_t flash_get_page_size(void) { return FLASH_CTRL_PARAM_BYTES_PER_PAGE; }

uint32_t flash_get_word_size(void) { return FLASH_CTRL_PARAM_BYTES_PER_WORD; }

void flash_write_scratch_reg(uint32_t value) {
  REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_SCRATCH_REG_OFFSET) = value;
}

uint32_t flash_read_scratch_reg(void) {
  return REG32(FLASH_CTRL0_BASE_ADDR + FLASH_CTRL_SCRATCH_REG_OFFSET);
}

bool flash_get_init_status(void) {
  mmio_region_t flash_ctrl_base =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  return mmio_region_get_bit32(flash_ctrl_base, FLASH_CTRL_STATUS_REG_OFFSET,
                               FLASH_CTRL_STATUS_INIT_WIP_BIT);
}

void flash_init(void) {
  mmio_region_t flash_ctrl_base =
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  mmio_region_write32(flash_ctrl_base, FLASH_CTRL_INIT_REG_OFFSET, 1);

  mmio_region_write32(flash_ctrl_base, FLASH_CTRL_EXEC_REG_OFFSET,
                      FLASH_CTRL_PARAM_EXEC_EN);
}
