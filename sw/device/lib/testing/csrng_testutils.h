// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_CSRNG_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_CSRNG_TESTUTILS_H_

#include "sw/device/lib/dif/dif_csrng.h"

/**
 * Wait for the `csrng` instance command interface to be ready to accept
 * commands. Aborts test execution if an error is found.
 */
void csrng_testutils_cmd_ready_wait(const dif_csrng_t *csrng);

/**
 * Runs CSRNG generate command.
 *
 * @param csrng A CSRNG handle.
 * @param output Output buffer.
 * @param output_len Number of words of entropy to write to output buffer.
 */
void csrng_testutils_cmd_generate_run(const dif_csrng_t *csrng,
                                      uint32_t *output, size_t output_len);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_CSRNG_TESTUTILS_H_
