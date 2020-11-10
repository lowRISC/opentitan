// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_FLASH_CTRL_H_

#include <stdbool.h>
#include <stdint.h>

// Flash memory base defines, _SZ are presented in bytes
#define FLASH_MEM_BASE_ADDR 0x20000000

/**
 * Flash bank IDs
 */
typedef enum bank_index { FLASH_BANK_0 = 0, FLASH_BANK_1 = 1 } bank_index_t;

/**
 * Flash partitions
 */
typedef enum partition_type {
  kDataPartition = 0,
  kInfoPartition = 1
} part_type_t;

/**
 * Memory protection configuration options.
 * Data partitions and Info partitions are handled differently.
 */
typedef struct mp_region {
  /** Which region to program for data partition.
      Which page to program for info partition.
   */
  uint32_t num;
  /** Region offset. */
  uint32_t base;
  /** Region config size. */
  uint32_t size;
  /** Region partition size. */
  part_type_t part;
  /** Read enable flag. */
  uint32_t rd_en;
  /** Program enable flag. */
  uint32_t prog_en;
  /** Erase enable flag. */
  uint32_t erase_en;
  /** Scramble / ECC enable flag. */
  uint32_t scramble_en;
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
 * Erase flash bank `bank_idx`. Blocks until erase is complete.
 *
 * @param idx Flash bank index.
 * @return Non zero on failure.
 */
int flash_bank_erase(bank_index_t idx);
int flash_page_erase(uint32_t addr, part_type_t part);

/**
 * Write `data` at `addr` offset with `size` in 4B words
 *
 * @param addr Flash address 32bit aligned.
 * @param part Flash parittion to access.
 * @param data Data to write.
 * @param size Number of 4B words to write from `data` buffer.
 * @return Non zero on failure.
 */
int flash_write(uint32_t addr, part_type_t part, const uint32_t *data,
                uint32_t size);

/**
 * Read `size` 4B words and write result to `data`.
 *
 * @param addr Read start address.
 * @param part Flash parittion to access.
 * @param size Number of 4B words to read.
 * @param[out] data Output buffer.
 * @return Non zero on failure.
 */
int flash_read(uint32_t addr, part_type_t part, uint32_t size, uint32_t *data);

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

/** Get number of flash banks */
uint32_t flash_get_banks(void);

/** Get number of pages per bank */
uint32_t flash_get_pages_per_bank(void);

/** Get number of words per page */
uint32_t flash_get_words_per_page(void);

/** Get size of each bank in bytes */
uint32_t flash_get_bank_size(void);

/** Get size of each page in bytes */
uint32_t flash_get_page_size(void);

/** Get size of each flash word in bytes */
uint32_t flash_get_word_size(void);

/** Write value to flash scratch register */
void flash_write_scratch_reg(uint32_t value);

/** Read scratch register */
uint32_t flash_read_scratch_reg(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_FLASH_CTRL_H_
