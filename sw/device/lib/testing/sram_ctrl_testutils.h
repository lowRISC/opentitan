// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_sram_ctrl.h"

/*
 * Adds the first parameter to the second parameter and returns the result.
 *
 * The main use-case is to map this function pointer onto a buffer holding
 * SRAM execution test instructions. The assumption is that this buffer holds
 * instruction[0] = add a0, a1, a0, instruction[1] = jalr zero, 0(ra).
 */
typedef uint32_t (*sram_ctrl_testutils_exec_function_t)(volatile uint32_t,
                                                        volatile uint32_t);

/**
 * A typed representation of the test data.
 */
#define SRAM_CTRL_DATA_NUM_WORDS 4
#define SRAM_CTRL_DATA_NUM_BYTES 128
typedef struct sram_ctrl_data {
  uint32_t words[SRAM_CTRL_DATA_NUM_WORDS];
} sram_ctrl_data_t;

/**
 * Writes `data` at the `address` in RAM.
 */
void sram_ctrl_testutils_write(uintptr_t address, const sram_ctrl_data_t *data);

/**
 * Reads data from `address` in SRAM and compares against `expected`.
 *
 * The data is checked for equality.
 */
bool sram_ctrl_testutils_read_check_eq(uintptr_t address,
                                       const sram_ctrl_data_t *expected);

/**
 * Reads data from `address` in SRAM and compares against `expected`.
 *
 * The data is checked for inequality.
 */
bool sram_ctrl_testutils_read_check_neq(uintptr_t address,
                                        const sram_ctrl_data_t *expected);

/**
 * Triggers the SRAM scrambling operation.
 *
 * SRAM Controller scrambling status is polled continuously. If the operation
 * has not finished in approximately 850 cycles, a timeout assertion occurs.
 * The SRAM documentation stated that the scrambling operation takes around
 * 800 cycles, so another 50 are added just to be on a safe side.
 */
void sram_ctrl_testutils_scramble(const dif_sram_ctrl_t *sram_ctrl);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_
