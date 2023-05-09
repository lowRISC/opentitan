// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

/**
 * Wait for the flash_ctrl to initialize.
 *
 * @param flash_state A flash_ctrl state handle.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_wait_for_init(
    dif_flash_ctrl_state_t *flash_state);

/**
 * Wait for a flash_ctrl operation to end.
 *
 * Calls dif_flash_ctrl_end in a loop and waits for a dif_result of Ok. If at
 * any time the result is BadArg or Error this will fail.
 * Clears any error codes and returns the value of operation_error.
 *
 * @param flash_state A flash_ctrl state handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_wait_transaction_end(
    dif_flash_ctrl_state_t *flash_state);

/**
 * Setup and enable for a data region taking region properties as a parameter.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param region_properties The properties for the data region.
 * @param region_properties The properties for the data region.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_data_region_setup_properties(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size,
    dif_flash_ctrl_region_properties_t region_properties, uint32_t *offset);

/**
 * Setup and enable for a data region with scrambling disabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_data_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size, uint32_t *offset);

/**
 * Setup and enable for a data region with scrambling enabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_data_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size, uint32_t *offset);

/**
 * Setup and enable for an info region taking region properties as a parameter.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param partition_id The partition index.
 * @param region_properties The properties for the info region.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_info_region_setup_properties(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id, dif_flash_ctrl_region_properties_t region_properties,
    uint32_t *offset);

/**
 * Setup and enable for an info region with scrambling disabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param partition_id The partition index.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_info_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id, uint32_t *offset);

/**
 * Setup and enable for an info region with scrambling enabled.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param page_id Region page index.
 * @param bank The required bank.
 * @param partition_id The partition index.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_info_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id, uint32_t *offset);

/**
 * Erases the page at byte_address.
 * Returns the result of transaction_end.
 *
 * @param flash_state A flash_ctrl state handle.
 * @param byte_address The byte address of the page to erase.
 * @param partition_id The partition index.
 * @param partition_type The partition type, data or info.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_erase_page(
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
 * @param word_count The number of uint32_t words to program.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_write(
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
 * @param partition_id The partition index.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of uint32_t words to program.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_erase_and_write_page(
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
 * @param word_count The number of uint32_t words to read.
 * @param delay_micros Optional delay (in us) for read FIFO fill testing.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_read(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, uint32_t *data_out,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count,
    uint32_t delay);

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
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_default_region_access(
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
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_bank_erase(dif_flash_ctrl_state_t *flash_state,
                                         uint32_t bank, bool data_only);

enum {
  kFlashCtrlTestUtilsCounterMaxCount = 256,
};

/**
 * Init the backdoor API, it should be called before
 * `flash_ctrl_testutils_backdoor_wait_update`.
 *
 * @param flash_state A flash_ctrl handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_backdoor_init(
    dif_flash_ctrl_state_t *flash_state);

/**
 * This is a backdoor API to be used with dvsim testbench.
 * Backdoor variables present on flash may not be updated when read by software
 * after written in the testbench due to the cache. So this function implements
 * a workaround to invalidate the cache and force it to update. Before using
 * this function `flash_ctrl_testutils_backdoor_init` should be called.
 *
 * @param flash_state A flash_ctrl handle.
 * @param addr The address to a `const uint32_t` variable where the testbench
 * will write to.
 * @param timeout Timeout.
 */
OT_WARN_UNUSED_RESULT
status_t flash_ctrl_testutils_backdoor_wait_update(
    dif_flash_ctrl_state_t *flash_state, uintptr_t addr, size_t timeout);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_FLASH_CTRL_TESTUTILS_H_
