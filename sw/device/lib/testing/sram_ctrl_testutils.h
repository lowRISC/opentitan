// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_sram_ctrl.h"

/**
 * Test buffer size in words and bytes.
 */
#define SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS 4
#define SRAM_CTRL_TESTUTILS_DATA_NUM_BYTES \
  (SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS * sizeof(uint32_t))

/**
 * A typed representation of the test data.
 */
typedef struct sram_ctrl_testutils_data {
  uint32_t words[SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS];
} sram_ctrl_testutils_data_t;

/**
 * Writes `data` at the `address` in RAM.
 */
void sram_ctrl_testutils_write(uintptr_t address,
                               const sram_ctrl_testutils_data_t data);

/**
 * Reads data from `address` in SRAM and compares against `expected`.
 *
 * The data is checked for equality.
 */
OT_WARN_UNUSED_RESULT
bool sram_ctrl_testutils_read_check_eq(
    uintptr_t address, const sram_ctrl_testutils_data_t expected);

/**
 * Reads data from `address` in SRAM and compares against `expected`.
 *
 * The data is checked for inequality.
 */
OT_WARN_UNUSED_RESULT
bool sram_ctrl_testutils_read_check_neq(
    uintptr_t address, const sram_ctrl_testutils_data_t expected);

/**
 * Triggers the SRAM scrambling operation.
 *
 * SRAM Controller scrambling status is polled continuously. If the operation
 * has not finished in approximately 850 cycles, a timeout assertion occurs.
 * The SRAM documentation stated that the scrambling operation takes around
 * 800 cycles, so another 50 are added just to be on a safe side.
 */
void sram_ctrl_testutils_scramble(const dif_sram_ctrl_t *sram_ctrl);

/**
 * Triggers the SRAM wipe operation and waits for it to finish.
 */
void sram_ctrl_testutils_wipe(const dif_sram_ctrl_t *sram_ctrl);

/**
 * Reads data from `backdoor_addr` in SRAM (retention or main) and
 * compares against `expected_bytes`.
 *
 * The data is checked for equality.
 */
void sram_ctrl_testutils_check_backdoor_write(uintptr_t backdoor_addr,
                                              uint32_t num_words,
                                              uint32_t offset_addr,
                                              const uint8_t *expected_bytes);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_
