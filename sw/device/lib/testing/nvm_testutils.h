// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"

/**
 * Logical NVM info pages known to the test infrastructure.
 *
 * Callers use these symbolic identifiers.  The mapping to physical page, bank,
 * and partition IDs lives entirely inside nvm_testutils.c and can be updated
 * when the underlying NVM technology changes.
 */
typedef enum nvm_info_page {
  kNvmInfoPageCreatorSecret = 0,
  kNvmInfoPageOwnerSecret = 1,
  kNvmInfoPageIsolated = 2,
} nvm_info_page_t;

/**
 * Write data to a logical NVM info page.
 *
 * Initialises the NVM controller internally, resolves the physical location
 * from `page`, configures the info region (with or without scrambling), erases
 * and programs the page, then verifies with a readback.  Callers do not need
 * to know physical page, bank, or partition IDs.
 *
 * @param page       Logical info page identifier.
 * @param data       Data words to write.
 * @param word_count Number of 32-bit words to write (max 64).
 * @param scramble   Whether to enable scrambling for this region.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_write_info_page(nvm_info_page_t page,
                                       const uint32_t *data, size_t word_count,
                                       bool scramble);

/**
 * Read data from a logical NVM info page.
 *
 * Initialises the NVM controller internally and resolves the physical location
 * from `page` before reading.
 *
 * @param page         Logical info page identifier.
 * @param[out] data    Output buffer for the read data.
 * @param word_count   Number of 32-bit words to read.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t nvm_testutils_read_info_page(nvm_info_page_t page, uint32_t *data,
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

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_NVM_TESTUTILS_H_
