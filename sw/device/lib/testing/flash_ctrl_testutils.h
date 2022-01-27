// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_flash_ctrl.h"

#define MAX_BEATS_PER_BURST 16

/**
 * Wait for a flash_ctrl operation to end.
 *
 * Calls dif_flash_ctrl_end in a loop and waits for a dif_result of Ok. If at
 * any time the result is BadArg or Error this will fail.
 * Clears any error codes and returns the value of operation_error.
 *
 * @param flash_state A flash_ctrl state handle.
 * @return The operation error flag.
 */
bool flash_ctrl_testutils_wait_transaction_end(
    dif_flash_ctrl_state_t *flash_state);

/**
 * Setup and enable for a data region.
 * Returns the address offset of the region.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_data_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size);

/**
 * Setup and enable for an info region.
 * Returns the address offset of the region.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param paritiion_id The partition index.
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_info_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id);

/**
 * Erases the page at byte_address.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase.
 * @param paritiion_id The partition index.
 * @param partition_type The partition type, data or info.
 * @return The operation error flag.
 */
bool flash_ctrl_testutils_erase_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, dif_flash_ctrl_partition_type_t partition_type);

/**
 * Programs the page at byte_address. The write is broken into
 * as many transactions as required for the supplied word_count such
 * that MAX_BEATS_PER_BURST is not exceded in any transaction.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to program.
 * @param paritiion_id The partition index.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of words to program.
 * @return The operation error flag.
 */
bool flash_ctrl_testutils_write_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, const uint32_t *data,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count);

/**
 * Erases and Programs the page at byte_address.
 * Calls the erase and write functions in turn.
 * Returns the combined result of the transaction_ends.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase and program.
 * @param paritiion_id The partition index.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of words to program.
 * @return The combined operation error flags from erase and program.
 */
bool flash_ctrl_testutils_erase_and_write_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, const uint32_t *data,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count);

/**
 * Reads the page at byte_address.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase and program.
 * @param paritiion_id The partition index.
 * @param data_out The data read from the page.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of words to read.
 * @return The operation error flag.
 */
bool flash_ctrl_testutils_read_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, uint32_t *data_out,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count,
    uint32_t delay);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_
