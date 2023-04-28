// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_CSRNG_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_CSRNG_TESTUTILS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_csrng.h"

/**
 * Wait for the `csrng` instance command interface to be ready to accept
 * commands. Aborts test execution if an error is found.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_cmd_ready_wait(const dif_csrng_t *csrng);

/**
 * Runs CSRNG generate command.
 *
 * @param csrng A CSRNG handle.
 * @param output Output buffer.
 * @param output_len Number of words of entropy to write to output buffer.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_cmd_generate_run(const dif_csrng_t *csrng,
                                          uint32_t *output, size_t output_len);

/**
 * Checks the CSRNG internal state against `expected` values.
 *
 * @param csrng A CSRNG handle.
 * @param expected Expected CSRNG internal state.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_check_internal_state(
    const dif_csrng_t *csrng, const dif_csrng_internal_state_t *expected);

/**
 * CTR_DRBG Known-Answer-Test (KAT) for INSTANTIATE command.
 *
 * @param csrng A CSRNG handle.
 * @param fail_expected Expected fail.
 * @param seed_material Seed material to use for the command.
 * @param expected_state Expected CSRNG internal state after the command.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_kat_instantiate(
    const dif_csrng_t *csrng, bool fail_expected,
    const dif_csrng_seed_material_t *seed_material,
    const dif_csrng_internal_state_t *expected_state);

/**
 * CTR_DRBG Known-Answer-Test (KAT) for GENERATE command.
 *
 * @param csrng A CSRNG handle.
 * @param num_generates Number of GENERATE commands to run.
 * @param output_len Number of output words to read from CSRNG after the last
 * command.
 * @param expected_output Expected CSRNG output after the last command.
 * @param expected_state Expected CSRNG internal state after the last command.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_kat_generate(
    const dif_csrng_t *csrng, uint32_t num_generates, uint32_t output_len,
    const uint32_t *expected_output,
    const dif_csrng_internal_state_t *expected_state);

/**
 * CTR_DRBG Known-Answer-Test (KAT) for RESEED command.
 *
 * @param csrng A CSRNG handle.
 * @param seed_material Seed material to use for the command.
 * @param expected_state Expected CSRNG internal state after the command.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_kat_reseed(
    const dif_csrng_t *csrng, const dif_csrng_seed_material_t *seed_material,
    const dif_csrng_internal_state_t *expected_state);

/**
 * CTR DRBG Known-Answer-Test (KAT) for INSTANTIATE command.
 *
 * @param csrng Handle.
 * @param fail_expected Expected fail.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_fips_instantiate_kat(const dif_csrng_t *csrng,
                                              bool fail_expected);

/**
 * CTR DRBG Known-Answer-Test (KAT) for GENERATE command.
 *
 * @param csrng Handle.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_fips_generate_kat(const dif_csrng_t *csrng);

/**
 * Checks CSRNG command status.
 *
 * Asserts error if the command or internal FIFO status contains any errors.
 *
 * @param csrng Handle.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_cmd_status_check(const dif_csrng_t *csrng);

/**
 * Checks CSRNG recoverable alerts.
 *
 * Asserts error if there are any CSRNG recoverable alerts set.
 *
 * @param csrng Handle.
 */
OT_WARN_UNUSED_RESULT
status_t csrng_testutils_recoverable_alerts_check(const dif_csrng_t *csrng);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_CSRNG_TESTUTILS_H_
