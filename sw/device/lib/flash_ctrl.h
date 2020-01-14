// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_FLASH_CTRL_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * Flash bank IDs
 */
typedef enum bank_index { FLASH_BANK_0 = 0, FLASH_BANK_1 = 1 } bank_index_t;

/**
 * Memory protection configuration options.
 */
typedef struct mp_region {
  /** Which region to program. */
  uint32_t num;
  /** Region offset. */
  uint32_t base;
  /** Region config size. */
  uint32_t size;
  /** Read enable flag. */
  uint32_t rd_en;
  /** Program enable flag. */
  uint32_t prog_en;
  /** Erase enable flag. */
  uint32_t erase_en;
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
int flash_page_erase(uint32_t addr);

/**
 * Write |data| at |addr| offset with |size| in 4B words
 *
 * @param addr Flash address 32bit aligned.
 * @param data Data to write.
 * @param size Number of 4B words to write from |data| buffer.
 * @return Non zero on failure.
 */
int flash_write(uint32_t addr, const uint32_t *data, uint32_t size);

/**
 * Read |size| 4B words and write result to |data|.
 *
 * @param addr Read start address.
 * @param size Number of 4B words to read.
 * @param data Output buffer.
 * @return Non zero on failure.
 */
int flash_read(uint32_t addr, uint32_t size, uint32_t *data);

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
void flash_write_scratch_reg(uint32_t value);

/** Read scratch register */
uint32_t flash_read_scratch_reg(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_FLASH_CTRL_H_
