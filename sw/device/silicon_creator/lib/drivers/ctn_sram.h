// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CTN_SRAM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CTN_SRAM_H_

#include "sw/lib/sw/device/base/hardened.h"
#include "sw/lib/sw/device/base/multibits.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Write data into CTN SRAM at a specific address.
 *
 * @param addr starting address to write data into sram.
 * @param len number of words of data to write into sram.
 * @param data data to write into sram.
 * @return Result of the operation.
 */
rom_error_t ctn_sram_data_write(uint32_t addr, uint32_t len, const void *data);

/*
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 2 -n 32 \
 *     -s 2181785819 --language=c
 *
 * Minimum Hamming distance: 14
 * Maximum Hamming distance: 14
 * Minimum Hamming weight: 14
 * Maximum Hamming weight: 18
 */

typedef enum ctn_sram_erase_type {
  /**
   * Erase a page.
   */
  kCtnSramEraseTypePage = 0xaf0eab8b,
  /**
   * Erase a bank.
   */
  kCtnSramEraseTypeBank = 0x80329be9,
} ctn_sram_erase_type_t;

/**
 * Erases a data partition page or bank.
 *
 * The flash controller will truncate to the closest page boundary for page
 * erase operations, and to the nearest bank aligned boundary for bank erase
 * operations.
 *
 * @param addr Address that falls within the bank or page being deleted.
 * @param erase_type Whether to erase a page or a bank.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t ctn_sram_data_erase(uint32_t addr,
                                ctn_sram_erase_type_t erase_type);

/**
 * Verifies that a data partition page or bank was erased.
 *
 * @param addr Address that falls within the bank or page erased.
 * @param erase_type Whether to verify a page or a bank.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t ctn_sram_data_erase_verify(uint32_t addr,
                                       ctn_sram_erase_type_t erase_type);

/**
 * A struct for specifying access permissions.
 *
 * ctn_sram config registers use 4-bits for boolean values. Use
 * `kMultiBitBool4True` to enable and `kMultiBitBool4False` to disable
 * permissions.
 *
 * Note: provided to maintain compatibility with flash controller
 */
typedef struct ctn_sram_perms {
  /**
   * Read.
   */
  multi_bit_bool_t read;
  /**
   * Write.
   */
  multi_bit_bool_t write;
  /**
   * Erase.
   */
  multi_bit_bool_t erase;
} ctn_sram_perms_t;

/**
 * Sets default access permissions for the data partition.
 *
 * A permission is enabled only if the corresponding field in `perms` is
 * `kMultiBitBool4True`.
 *
 * Note: provided to maintain compatibility with flash controller
 *
 * @param perms New permissions.
 */
void ctn_sram_data_default_perms_set(ctn_sram_perms_t perms);

/**
 * Set bank erase permissions for both flash banks.
 *
 * Note: provided to maintain compatibility with flash controller
 *
 * @param enable Whether to enable bank erase.
 */
void ctn_sram_bank_erase_perms_set(hardened_bool_t enable);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CTN_SRAM_H_
