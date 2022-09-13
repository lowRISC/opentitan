// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_flash_ctrl.h"

/**
 * Wait for the flash_ctrl to initialize.
 *
 * @param flash_state A flash_ctrl state handle.
 */
void flash_ctrl_testutils_wait_for_init(dif_flash_ctrl_state_t *flash_state);

/**
 * Wait for a flash_ctrl operation to end.
 *
 * Calls dif_flash_ctrl_end in a loop and waits for a dif_result of Ok. If at
 * any time the result is BadArg or Error this will fail.
 * Clears any error codes and returns the value of operation_error.
 *
 * @param flash_state A flash_ctrl state handle.
 * @return False if the operation produced an error.
 */
OT_WARN_UNUSED_RESULT
bool flash_ctrl_testutils_wait_transaction_end(
    dif_flash_ctrl_state_t *flash_state);

/**
 * Setup and enable for a data region taking region properties as a parameter.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param region_properties The properties for the data region.
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_data_region_setup_properties(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size,
    dif_flash_ctrl_region_properties_t region_properties);

/**
 * Setup and enable for a data region with scrambling disabled.
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
 * Setup and enable for a data region with scrambling enabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_data_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size);

/**
 * Setup and enable for an info region taking region properties as a parameter.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param partition_id The partition index.
 * @param region_properties The properties for the info region.
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_info_region_setup_properties(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id,
    dif_flash_ctrl_region_properties_t region_properties);

/**
 * Setup and enable for an info region with scrambling disabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param partition_id The partition index.
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_info_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id);

/**
 * Setup and enable for an info region with scrambling enabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param partition_id The partition index.
 * @return The byte address offset of the region.
 */
uint32_t flash_ctrl_testutils_info_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id);

/**
 * Erases the page at byte_address.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase.
 * @param partition_id The partition index.
 * @param partition_type The partition type, data or info.
 * @return False if the operation failed.
 */
OT_WARN_UNUSED_RESULT
bool flash_ctrl_testutils_erase_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, dif_flash_ctrl_partition_type_t partition_type);

/**
 * Programs the flash starting from byte_address.
 * The write is broken into as many transactions as required for the supplied
 * word_count such that the program resolution is not exceeded in any
 * transaction.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to program.
 * @param partition_id The partition index.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of words to program.
 * @return False if the operation produced an error.
 */
OT_WARN_UNUSED_RESULT
bool flash_ctrl_testutils_write(dif_flash_ctrl_state_t *flash_state,
                                uint32_t byte_address, uint32_t partition_id,
                                const uint32_t *data,
                                dif_flash_ctrl_partition_type_t partition_type,
                                uint32_t word_count);

/**
 * Erases and Programs the page at byte_address.
 * Calls the erase and write functions in turn.
 * Returns the combined result of the transaction_ends.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase and program.
 * @param partition_id The partition index.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of words to program.
 * @return False if the operation fails.
 */
OT_WARN_UNUSED_RESULT
bool flash_ctrl_testutils_erase_and_write_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, const uint32_t *data,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count);

/**
 * Reads data starting from byte_address.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase and program.
 * @param partition_id The partition index.
 * @param data_out The data read from the page.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of words to read.
 * @return The operation error flag.
 */
OT_WARN_UNUSED_RESULT
bool flash_ctrl_testutils_read(dif_flash_ctrl_state_t *flash_state,
                               uint32_t byte_address, uint32_t partition_id,
                               uint32_t *data_out,
                               dif_flash_ctrl_partition_type_t partition_type,
                               uint32_t word_count, uint32_t delay);

/**
 * Sets the flash default configuration.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param rd_en Default read enable.
 * @param prog_en Default program enable.
 * @param erase_en Default page erase enable.
 * @param scramble_en Default scramble enable.
 * @param ecc_en Default ECC enable.
 * @param high_endurance_en Default high endurance enable
 */
void flash_ctrl_testutils_default_region_access(
    dif_flash_ctrl_state_t *flash_state, bool rd_en, bool prog_en,
    bool erase_en, bool scramble_en, bool ecc_en, bool high_endurance_en);

/**
 * Enables erase for the provided bank, erases the bank, then disables bank
 * erase.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param bank The bank ID.
 * @param data_only True to only erase the data partitions. False to erase
 *                  everything.
 * @return False if the operation failed.
 */
OT_WARN_UNUSED_RESULT
bool flash_ctrl_testutils_bank_erase(dif_flash_ctrl_state_t *flash_state,
                                     uint32_t bank, bool data_only);

enum {
  kFlashCtrlTestUtilsCounterMaxCount = 256,
};

/**
 * Returns the value of a non-volatile counter in flash.
 *
 * @param counter Counter ID, [0, 2].
 * @return Value of the non-volatile counter
 */
uint32_t flash_ctrl_testutils_counter_get(size_t counter);

/**
 * Increments a non-volatile counter in flash.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param counter Counter ID, [0, 2].
 */
void flash_ctrl_testutils_counter_increment(dif_flash_ctrl_state_t *flash_state,
                                            size_t counter);

/**
 * Sets a non-volatile counter to at least `val`.
 *
 * This function simply writes zeros to the corresponding flash word without any
 * checks and is intended for contexts where performance is critical, e.g. ISRs.
 * The value of the counter will not change if it is already greater than or
 * equal to `val`.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param counter Counter ID, [0, 2].
 * @param val Counter value.
 */
void flash_ctrl_testutils_counter_set_at_least(
    dif_flash_ctrl_state_t *flash_state, size_t counter, uint32_t val);

/**
 * Sets a strike counter to an arbitrary value.
 *
 * If the arbitrary value is impossible (attempts to flip a bit
 * from 0 to 1 without an erase), an error is created.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param strike_counter The address of the counter.
 * @param new_val The new counter value.
 */
void flash_ctrl_testutils_set_counter(dif_flash_ctrl_state_t *flash_state,
                                      uint32_t *strike_counter,
                                      uint32_t new_val);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_
