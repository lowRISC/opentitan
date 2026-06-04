// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_nvm_ctrl.h"

// NVM test utilities — technology-agnostic wrappers over flash_ctrl_testutils.
//
// All test code that needs to touch NVM should call nvm_testutils_* functions
// and hold dif_nvm_ctrl_state_t handles.  The mapping to flash_ctrl_testutils
// lives in nvm_testutils.c.

/**
 * Wait for the NVM controller to initialise.
 *
 * @param nvm NVM controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_wait_for_init(dif_nvm_ctrl_state_t *nvm);

/**
 * Wait for an in-progress NVM operation to complete.
 *
 * @param nvm NVM controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_wait_transaction_end(dif_nvm_ctrl_state_t *nvm);

/**
 * Configure and enable a data region with caller-supplied properties.
 *
 * @param nvm              NVM controller handle.
 * @param base_page_index  Region base page index.
 * @param data_region      Region index.
 * @param region_size      Region size in pages.
 * @param region_properties Properties to apply.
 * @param[out] offset      Byte address of the region start.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_data_region_setup_properties(
    dif_nvm_ctrl_state_t *nvm, uint32_t base_page_index, uint32_t data_region,
    uint32_t region_size, dif_nvm_ctrl_region_properties_t region_properties,
    uint32_t *offset);

/**
 * Configure and enable a data region with scrambling disabled.
 *
 * @param nvm              NVM controller handle.
 * @param base_page_index  Region base page index.
 * @param data_region      Region index.
 * @param region_size      Region size in pages.
 * @param[out] offset      Byte address of the region start.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_data_region_setup(dif_nvm_ctrl_state_t *nvm,
                                         uint32_t base_page_index,
                                         uint32_t data_region,
                                         uint32_t region_size,
                                         uint32_t *offset);

/**
 * Configure and enable a data region with scrambling enabled.
 *
 * @param nvm              NVM controller handle.
 * @param base_page_index  Region base page index.
 * @param data_region      Region index.
 * @param region_size      Region size in pages.
 * @param[out] offset      Byte address of the region start.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_data_region_scrambled_setup(dif_nvm_ctrl_state_t *nvm,
                                                   uint32_t base_page_index,
                                                   uint32_t data_region,
                                                   uint32_t region_size,
                                                   uint32_t *offset);

/**
 * Configure and enable an info region with caller-supplied properties.
 *
 * @param nvm              NVM controller handle.
 * @param page_id          Region page index.
 * @param bank             Bank index.
 * @param partition_id     Partition index.
 * @param region_properties Properties to apply.
 * @param[out] offset      Byte address of the region start.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_region_setup_properties(
    dif_nvm_ctrl_state_t *nvm, uint32_t page_id, uint32_t bank,
    uint32_t partition_id, dif_nvm_ctrl_region_properties_t region_properties,
    uint32_t *offset);

/**
 * Configure and enable an info region with scrambling disabled.
 *
 * @param nvm          NVM controller handle.
 * @param page_id      Region page index.
 * @param bank         Bank index.
 * @param partition_id Partition index.
 * @param[out] offset  Byte address of the region start.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_region_setup(dif_nvm_ctrl_state_t *nvm,
                                         uint32_t page_id, uint32_t bank,
                                         uint32_t partition_id,
                                         uint32_t *offset);

/**
 * Configure and enable an info region with scrambling enabled.
 *
 * @param nvm          NVM controller handle.
 * @param page_id      Region page index.
 * @param bank         Bank index.
 * @param partition_id Partition index.
 * @param[out] offset  Byte address of the region start.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_region_scrambled_setup(dif_nvm_ctrl_state_t *nvm,
                                                   uint32_t page_id,
                                                   uint32_t bank,
                                                   uint32_t partition_id,
                                                   uint32_t *offset);

/**
 * Erase the page at byte_address.
 *
 * @param nvm            NVM controller handle.
 * @param byte_address   Byte address of the page to erase.
 * @param partition_id   Partition index.
 * @param partition_type Partition type (data or info).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_erase_page(dif_nvm_ctrl_state_t *nvm,
                                  uint32_t byte_address, uint32_t partition_id,
                                  dif_nvm_ctrl_partition_type_t partition_type);

/**
 * Program words starting at byte_address.
 *
 * @param nvm            NVM controller handle.
 * @param byte_address   Start byte address.
 * @param partition_id   Partition index.
 * @param data           Data to program.
 * @param partition_type Partition type (data or info).
 * @param word_count     Number of 32-bit words to program.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_write(dif_nvm_ctrl_state_t *nvm, uint32_t byte_address,
                             uint32_t partition_id, const uint32_t *data,
                             dif_nvm_ctrl_partition_type_t partition_type,
                             uint32_t word_count);

/**
 * Erase then program the page at byte_address.
 *
 * @param nvm            NVM controller handle.
 * @param byte_address   Byte address of the page to erase and program.
 * @param partition_id   Partition index.
 * @param data           Data to program.
 * @param partition_type Partition type (data or info).
 * @param word_count     Number of 32-bit words to program.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_erase_and_write_page(
    dif_nvm_ctrl_state_t *nvm, uint32_t byte_address, uint32_t partition_id,
    const uint32_t *data, dif_nvm_ctrl_partition_type_t partition_type,
    uint32_t word_count);

/**
 * Read words starting at byte_address.
 *
 * @param nvm            NVM controller handle.
 * @param byte_address   Start byte address.
 * @param partition_id   Partition index.
 * @param[out] data_out  Output buffer.
 * @param partition_type Partition type (data or info).
 * @param word_count     Number of 32-bit words to read.
 * @param delay          Optional delay in microseconds (0 for none).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_read(dif_nvm_ctrl_state_t *nvm, uint32_t byte_address,
                            uint32_t partition_id, uint32_t *data_out,
                            dif_nvm_ctrl_partition_type_t partition_type,
                            uint32_t word_count, uint32_t delay);

/**
 * Set the default data region access permissions.
 *
 * @param nvm               NVM controller handle.
 * @param rd_en             Enable reads.
 * @param prog_en           Enable programming.
 * @param erase_en          Enable erasing.
 * @param scramble_en       Enable scrambling.
 * @param ecc_en            Enable ECC.
 * @param high_endurance_en Enable high-endurance mode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_default_region_access(dif_nvm_ctrl_state_t *nvm,
                                             bool rd_en, bool prog_en,
                                             bool erase_en, bool scramble_en,
                                             bool ecc_en,
                                             bool high_endurance_en);

/**
 * Erase a full bank.
 *
 * @param nvm       NVM controller handle.
 * @param bank      Bank index.
 * @param data_only True to erase data partitions only.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_bank_erase(dif_nvm_ctrl_state_t *nvm, uint32_t bank,
                                  bool data_only);

enum {
  kNvmTestutilsCounterMaxCount = 256,
};

/**
 * Log any fault status bits set in the NVM controller.
 *
 * @param nvm NVM controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_show_faults(const dif_nvm_ctrl_state_t *nvm);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
