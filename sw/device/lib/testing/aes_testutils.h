// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_

#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

/**
 * Returns the value of the AES status flag.
 *
 * @param aes An aes DIF handle.
 * @param flag Status flag to query.
 */
inline bool aes_testutils_get_status(dif_aes_t *aes, dif_aes_status_t flag) {
  bool status;
  CHECK_DIF_OK(dif_aes_get_status(aes, flag, &status));
  return status;
}

/**
 * Waits for the given AES status flag to be set the the given value.
 *
 * @param aes An aes DIF handle.
 * @param flag Status flag to query.
 * @param value The status flag value.
 * @param timeout_usec Timeout in microseconds.
 */
#define AES_TESTUTILS_WAIT_FOR_STATUS(aes_, flag_, value_, timeout_usec_) \
  IBEX_SPIN_FOR(aes_testutils_get_status((aes_), (flag_)) == (value_),    \
                (timeout_usec_))

#if !OT_IS_ENGLISH_BREAKFAST
/**
 * Initializes the entropy complex for performing AES SCA measurements with
 * masking switched off.
 *
 * Initializes CSRNG and EDN0 to produce a fixed seed which after being loaded
 * into AES causes the AES masking PRNG to output an all-zero vector. Entropy
 * src and EDN1 are left untouched.
 */
void aes_testutils_masking_prng_zero_output_seed(void);

/**
 * CTR_DRBG Known-Answer-Test (KAT) using the CSRNG SW application interface.
 *
 * Initializes CSRNG and then runs multiple generate and a reseed command to
 * ensure the seed leading to an all-zero output of the AES masking PRNG can
 * repeatedly be generated.
 */
void aes_testutils_csrng_kat(void);
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_
