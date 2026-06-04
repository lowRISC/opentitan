// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include "hw/top/flash_ctrl_regs.h"  // Generated.

/** Size of a logical NVM info page in bytes. */
#define NVM_INFO_PAGE_SIZE FLASH_CTRL_PARAM_BYTES_PER_PAGE

/**
 * Logical NVM info page identifiers.
 *
 * Each constant identifies one info partition page.  The mapping to physical
 * (page_id, bank, partition_id) lives in nvm_testutils.c and can be updated
 * when the underlying NVM technology changes.
 */
typedef enum nvm_info_page {
  kNvmInfoPageFactory = 0,              // Bank 0, Page 0: wafer / CP / AST data
  kNvmInfoPageCreatorSecret = 1,        // Bank 0, Page 1
  kNvmInfoPageOwnerSecret = 2,          // Bank 0, Page 2
  kNvmInfoPageWaferAuthSecret = 3,      // Bank 0, Page 3
  kNvmInfoPageAttestationKeySeeds = 4,  // Bank 0, Page 4
} nvm_info_page_t;

/**
 * Write data to a logical NVM info page.
 *
 * Initialises the NVM controller internally, resolves the physical location
 * from `page`, configures the info region (with or without scrambling), and
 * programs the page.  When `erase_before_write` is true the page is erased
 * first and a readback is performed to verify the write.
 *
 * @param page               Logical info page identifier.
 * @param byte_offset        Byte offset from the start of the page.
 * @param data               Data words to write.
 * @param word_count         Number of 32-bit words to write (max 64).
 * @param scramble           Whether to enable scrambling for this region.
 * @param erase_before_write Erase the page before writing.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_write_info_page(nvm_info_page_t page,
                                       uint32_t byte_offset,
                                       const uint32_t *data, size_t word_count,
                                       bool scramble, bool erase_before_write);

/**
 * Read data from a logical NVM info page.
 *
 * Initialises the NVM controller internally and resolves the physical location
 * from `page` before reading.
 *
 * @param page         Logical info page identifier.
 * @param byte_offset  Byte offset from the start of the page.
 * @param[out] data    Output buffer for the read data.
 * @param word_count   Number of 32-bit words to read.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_read_info_page(nvm_info_page_t page,
                                      uint32_t byte_offset, uint32_t *data,
                                      size_t word_count);

/**
 * Configure the NVM controller default data region access permissions.
 *
 * Initialises the NVM controller internally and sets the default region
 * properties.  Callers do not need to hold a controller handle.  Hardware
 * register state persists, so subsequent NVM operations issued by other
 * utilities (e.g. nv_counter_testutils) will observe these settings.
 *
 * @param rd_en            Enable reads.
 * @param prog_en          Enable programming.
 * @param erase_en         Enable erasing.
 * @param scramble_en      Enable scrambling.
 * @param ecc_en           Enable ECC.
 * @param high_endurance_en Enable high-endurance mode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_enable_data_access(bool rd_en, bool prog_en,
                                          bool erase_en, bool scramble_en,
                                          bool ecc_en, bool high_endurance_en);

/**
 * Configure an NVM info region for scrambled access.
 *
 * Initialises the NVM controller internally and sets up the info region at
 * (page_id, bank, partition_id) with scrambling enabled.  Returns the byte
 * address of the page in `offset`.  Callers do not need to hold a controller
 * handle.
 *
 * @param page_id      Info page index within the bank.
 * @param bank         Bank index.
 * @param partition_id Info partition ID.
 * @param[out] offset  Byte address of the page.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_region_setup(uint32_t page_id, uint32_t bank,
                                         uint32_t partition_id,
                                         uint32_t *offset);

OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_region_scrambled_setup(uint32_t page_id,
                                                   uint32_t bank,
                                                   uint32_t partition_id,
                                                   uint32_t *offset);

/**
 * Configure an NVM info region with caller-supplied properties.
 *
 * Initialises the NVM controller internally and sets up the info region at
 * (page_id, bank, partition_id) using the provided region properties.  Returns
 * the byte address of the page in `offset`.  Callers do not need to hold a
 * controller handle.
 *
 * @param page_id      Info page index within the bank.
 * @param bank         Bank index.
 * @param partition_id Info partition ID.
 * @param props        Region properties to apply.
 * @param[out] offset  Byte address of the page.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_info_region_setup_properties(
    uint32_t page_id, uint32_t bank, uint32_t partition_id,
    dif_flash_ctrl_region_properties_t props, uint32_t *offset);

/**
 * Configure access permissions for an NVM info page.
 *
 * Initialises the NVM controller internally and sets up the info region at
 * (page_id, bank, partition_id) with the given individual permission flags.
 * Returns the byte address of the page in `offset`.  Callers do not need to
 * hold a controller handle or use any flash-specific types.
 *
 * @param page_id           Info page index within the bank.
 * @param bank              Bank index.
 * @param partition_id      Info partition ID.
 * @param rd_en             Enable reads.
 * @param prog_en           Enable programming.
 * @param erase_en          Enable erasing.
 * @param scramble_en       Enable scrambling.
 * @param ecc_en            Enable ECC.
 * @param high_endurance_en Enable high-endurance mode.
 * @param[out] offset       Byte address of the page.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_set_info_page_access(uint32_t page_id, uint32_t bank,
                                            uint32_t partition_id, bool rd_en,
                                            bool prog_en, bool erase_en,
                                            bool scramble_en, bool ecc_en,
                                            bool high_endurance_en,
                                            uint32_t *offset);

/**
 * Erase and write an NVM info page at a raw byte address.
 *
 * Initialises the NVM controller internally, erases the info page that
 * contains `byte_address`, then programs `word_count` words of `data`
 * starting at `byte_address`.  The partition is identified by `partition_id`.
 *
 * @param byte_address Byte address of the start of the page to erase/write.
 * @param partition_id Info partition ID.
 * @param data         Data words to write.
 * @param word_count   Number of 32-bit words to write.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_erase_and_write_info_page(uint32_t byte_address,
                                                 uint32_t partition_id,
                                                 const uint32_t *data,
                                                 size_t word_count);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
