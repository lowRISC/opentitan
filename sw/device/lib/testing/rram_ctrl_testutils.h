// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RRAM_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RRAM_CTRL_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rram_ctrl.h"

/**
 * Wait for the rram_ctrl to initialize.
 *
 * @param rram_state A rram_ctrl state handle.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_wait_for_init(dif_rram_ctrl_state_t *rram_state);

/**
 * Wait for a rram_ctrl operation to end.
 *
 * Calls dif_rram_ctrl_end in a loop and waits for a dif_result of Ok. If at
 * any time the result is BadArg or Error this will fail.
 * Clears any error codes and returns the value of operation_error.
 *
 * @param rram_state A rram_ctrl state handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_wait_transaction_end(
    dif_rram_ctrl_state_t *rram_state);

/**
 * Setup and enable for a data region taking region properties as a parameter.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param region_properties The properties for the data region.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_data_region_setup_properties(
    dif_rram_ctrl_state_t *rram_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size,
    dif_rram_ctrl_region_properties_t region_properties, uint32_t *offset);

/**
 * Setup and enable for a data region with scrambling disabled.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_data_region_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size, uint32_t *offset);

/**
 * Setup and enable for a data region with scrambling enabled.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param base_page_index The region base page index.
 * @param data_region The region index.
 * @param region_size The region size (in number of pages).
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_data_region_scrambled_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size, uint32_t *offset);

/**
 * Setup and enable for an info region taking region properties as a parameter.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param page_id Region page index.
 * @param region_properties The properties for the info region.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_info_region_setup_properties(
    dif_rram_ctrl_state_t *rram_state, uint32_t page_id,
    dif_rram_ctrl_region_properties_t region_properties, uint32_t *offset);

/**
 * Setup and enable for an info region with scrambling disabled.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param page_id Region page index.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_info_region_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t page_id, uint32_t *offset);

/**
 * Setup and enable for an info region with scrambling enabled.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param page_id Region page index.
 * @param[out] offset The byte address offset of the region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_info_region_scrambled_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t page_id, uint32_t *offset);

/**
 * Write RRAM starting from byte_address.
 * The write is broken into as many transactions as required for the supplied
 * word_count exceeds the maximum supported size.
 * Returns the result of transaction_end.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param byte_address The byte address of the page to program.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of uint32_t words to program.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_write(
    dif_rram_ctrl_state_t *rram_state, uint32_t byte_address,
    const uint32_t *data, dif_rram_ctrl_partition_type_t partition_type,
    uint32_t word_count);

/**
 * Write a single 32b word to RRAM.
 * A full RRAM line is read, modified and written back to the RRAM
 * Returns the result of transaction_end.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param byte_address The byte address of the page to program.
 * @param data The data to program.
 * @param partition_type The partition type, data or info.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_write_word(
    dif_rram_ctrl_state_t *rram_state, uint32_t byte_address,
    const uint32_t *data, dif_rram_ctrl_partition_type_t partition_type);

/**
 * Reads data starting from byte_address.
 * Returns the result of transaction_end.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param byte_address The byte address of the page to erase and program.
 * @param data_out The data read from the page.
 * @param partition_type The partition type, data or info.
 * @param word_count The number of uint32_t words to read.
 * @param delay_micros Optional delay (in us) for read FIFO fill testing.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_read(dif_rram_ctrl_state_t *rram_state,
                                  uint32_t byte_address, uint32_t *data_out,
                                  dif_rram_ctrl_partition_type_t partition_type,
                                  uint32_t word_count, uint32_t delay);

/**
 * Sets the RRAM default configuration.
 *
 * @param rram_state A rram_ctrl state handle.
 * @param rd_en Default read enable.
 * @param wr_en Default program enable.
 * @param scramble_en Default scramble enable.
 * @param ecc_en Default ECC enable.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_default_region_access(
    dif_rram_ctrl_state_t *rram_state, bool rd_en, bool wr_en, bool scramble_en,
    bool ecc_en);

/**
 * Write to log any faults set in the status register.
 *
 * @param rram_state A rram_ctrl state handle.
 */
OT_WARN_UNUSED_RESULT
status_t rram_ctrl_testutils_show_faults(
    const dif_rram_ctrl_state_t *rram_state);

/**
 * Print the properties of a RRAM data region configuration.
 *
 * This prints:
 *
 * data region n=<index> st=<start> sz=<size> RD-WR-SC-EC LK
 *
 * The various properties are printed depending on their mubi bool value:
 * - The property (e.g. `RD`, `WR`, etc) is printed if enabled by Mubi4True.
 * - The string `xx` is printed if disabled by Mubi4False.
 * - The string `uu` is printed if disabled by any other non-True value.
 *
 * @param index The index of the region.
 * @param p The properties of the region.
 * @param locked Whether or not the region is locked.
 */
void rram_ctrl_testutils_data_region_print(
    size_t index, dif_rram_ctrl_data_region_properties_t *p, bool locked);

/**
 * Print the properties of a RRAM data region configuration.
 *
 * This prints:
 *
 * info region page=<page> RD-WR-SC-EC LK
 *
 * The various properties are printed depending on their mubi bool value:
 * - The property (e.g. `RD`, `WR`, etc) is printed if enabled by Mubi4True.
 * - The string `xx` is printed if disabled by Mubi4False.
 * - The string `uu` is printed if disabled by any other non-True value.
 *
 * @param region The info region descriptor.
 * @param p The properties of the region.
 * @param locked Whether or not the region is locked.
 */
void rram_ctrl_testutils_info_region_print(dif_rram_ctrl_info_region_t region,
                                           dif_rram_ctrl_region_properties_t *p,
                                           bool locked);
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RRAM_CTRL_TESTUTILS_H_
