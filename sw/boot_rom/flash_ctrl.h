// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _F_FLASH_CTRL_H__
#define _F_FLASH_CTRL_H__

#include <stdbool.h>
#include <stdint.h>

/**
 * Flash bank IDs
 */
typedef enum bank_index { FlashBank0 = 0, FlashBank1 = 1 } bank_index_t;

/**
 * Block until flash is initialized.
 */
void flash_init_block(void);

/**
 * Returns 1 if flash is empty, otherwise 0.
 */
int flash_check_empty(void);

/*
 * Erase flash bank |bank_idx|. Blocks until erase is complete.
 *
 * @param idx Flash bank index.
 * @return Non zero on failure.
 */
int flash_bank_erase(bank_index_t idx);

/**
 * Write |data| at |addr| offset with |size| in 4B words
 *
 * @param addr Flash address 32bit aligned.
 * @param data Data to write.
 * @param size Number of bytes to write from |data| buffer.
 */
int flash_write(uint32_t addr, const uint32_t *data, uint32_t size);

/**
 * Set flash controller default permissions.
 *
 * @param rd_end Read enable.
 * @param prog_en Write enable.
 * @param erase_en Erase enable.
 */
void flash_default_region_access(bool rd_en, bool prog_en, bool erase_en);

#endif  // _F_FLASH_CTRL_H__
