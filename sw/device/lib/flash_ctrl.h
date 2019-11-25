// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _F_FLASH_CTRL_H__
#define _F_FLASH_CTRL_H__

#include "sw/device/lib/base/types.h"

/**
 * Flash bank IDs
 */
typedef enum bank_index { FLASH_BANK_0 = 0, FLASH_BANK_1 = 1 } bank_index_t;

/**
 * Memory protection configuration options.
 */
typedef struct mp_region {
  /** Which region to program. */
  uint32 num;
  /** Region offset. */
  uint32 base;
  /** Region config size. */
  uint32 size;
  /** Read enable flag. */
  uint32 rd_en;
  /** Program enable flag. */
  uint32 prog_en;
  /** Erase enable flag. */
  uint32 erase_en;
} mp_region_t;

/**
 * Block until flash is initialized.
 */
void flash_init_block(void);

/**
 * Returns 1 if flash is empty, otherwise 0.
 */
int flash_check_empty(void);

/**
 * Erase flash bank |bank_idx|. Blocks until erase is complete.
 *
 * @param idx Flash bank index.
 * @return Non zero on failure.
 */
int flash_bank_erase(bank_index_t idx);
int flash_page_erase(uint32 addr);

/**
 * Write |data| at |addr| offset with |size| in 4B words
 *
 * @param addr Flash address 32bit aligned.
 * @param data Data to write.
 * @param size Number of 4B words to write from |data| buffer.
 * @return Non zero on failure.
 */
int flash_write(uint32 addr, const uint32 *data, uint32 size);

/**
 * Read |size| 4B words and write result to |data|.
 *
 * @param addr Read start address.
 * @param size Number of 4B words to read.
 * @param data Output buffer.
 * @return Non zero on failure.
 */
int flash_read(uint32 addr, uint32 size, uint32 *data);

/**
 * Configure bank erase enable
 */
void flash_cfg_bank_erase(bank_index_t bank, bool erase_en);

/**
 * Set flash controller default permissions.
 *
 * @param rd_end Read enable.
 * @param prog_en Write enable.
 * @param erase_en Erase enable.
 */
void flash_default_region_access(bool rd_en, bool prog_en, bool erase_en);

/**
 * Configure memory protection region.
 *
 * @param region_cfg Region configuration.
 */
void flash_cfg_region(const mp_region_t *region_cfg);

/** Write value to flash scratch register */
void flash_write_scratch_reg(uint32 value);

/** Read scratch register */
uint32 flash_read_scratch_reg(void);

#endif  // _F_FLASH_CTRL_H__
