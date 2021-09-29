// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_sram_ctrl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Parameters to be used in utility functions and SRAM tests.
 *
 * Note: utility and SRAM tests will use only a subset of the parameters
 *       that are relevant for the particular use-case.
 */
typedef struct sram_ctrl_params {
  /**
   * SRAM Controller register base.
   */
  uintptr_t reg_base;
  /**
   * SRAM Controller RAM start address (including the first word).
   */
  uintptr_t ram_start;
  /**
   * SRAM Controller RAM end address (including the last word).
   */
  uintptr_t ram_end;
} sram_ctrl_params_t;

/**
 * SRAM Controller type.
 */
typedef struct sram_ctrl {
  /**
   * SRAM Controller parameters.
   */
  const sram_ctrl_params_t *params;
  /**
   * SRAM Controller peripheral interface.
   */
  dif_sram_ctrl_t dif;
} sram_ctrl_t;

/**
 * A typed representation of the test data.
 */
#define SRAM_CTRL_DATA_NUM_WORDS 4
#define SRAM_CTRL_DATA_NUM_BYTES 128
typedef struct sram_ctrl_data {
  uint32_t words[SRAM_CTRL_DATA_NUM_WORDS];
} sram_ctrl_data_t;

/**
 * Initialize Main SRAM Controller.
 */
sram_ctrl_t sram_ctrl_main_init(void);

/**
 * Initialize Retention SRAM Controller.
 */
sram_ctrl_t sram_ctrl_ret_init(void);

/**
 * Writes data to the beginning and end of RAM.
 */
void sram_ctrl_write_to_ram(const sram_ctrl_t *sram,
                            const sram_ctrl_data_t *data_in);

/**
 * Reads and compares data at the beginning and end of RAM.
 *
 * The read data is checked for equality against the `expected` data.
 */
bool sram_ctrl_read_from_ram_eq(const sram_ctrl_t *sram,
                                const sram_ctrl_data_t *expected);

/**
 * Reads and compares data at the beginning and end of RAM.
 *
 * The read data is checked for inequality against the `expected` data.
 */
bool sram_ctrl_read_from_ram_neq(const sram_ctrl_t *sram,
                                 const sram_ctrl_data_t *expected);

/**
 * Triggers the SRAM scrambling operation.
 *
 * SRAM Controller scrambling status is polled continuously. If the operation
 * has not finished in approximately 850 cycles, a timeout assertion occurs.
 * The SRAM documentation stated that the scrambling operation takes around
 * 800 cycles, so another 50 are added just to be on a safe side.
 */
void sram_ctrl_scramble(const sram_ctrl_t *sram);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SRAM_CTRL_TESTUTILS_H_
