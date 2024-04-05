// Copyright lowRISC contributors (OpenTitan project).
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
 * @param status Status value to query.
 */
inline bool aes_testutils_get_status(dif_aes_t *aes, dif_aes_status_t status) {
  bool set;
  dif_result_t res = dif_aes_get_status(aes, status, &set);
  return (res == kDifOk) && set;
}

/**
 * Waits for the given AES status flag to be set the given value.
 *
 * @param aes An aes DIF handle.
 * @param flag Status flag value.
 * @param status The status value.
 * @param timeout_usec Timeout in microseconds.
 */
#define AES_TESTUTILS_WAIT_FOR_STATUS(aes_, status_, flag_, timeout_usec_)  \
  IBEX_TRY_SPIN_FOR(aes_testutils_get_status((aes_), (status_)) == (flag_), \
                    (timeout_usec_))

#if !OT_IS_ENGLISH_BREAKFAST
/**
 * Initializes the entropy complex for performing AES SCA measurements with
 * masking switched off.
 *
 * Initializes CSRNG and EDN0 to produce a fixed seed which after being loaded
 * into AES causes the AES masking PRNG to output an all-zero vector. Entropy
 * src and EDN1 are left untouched.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aes_testutils_masking_prng_zero_output_seed(void);

/**
 * CTR_DRBG Known-Answer-Test (KAT) using the CSRNG SW application interface.
 *
 * Initializes CSRNG and then runs multiple generate and a reseed command to
 * ensure the seed leading to an all-zero output of the AES masking PRNG can
 * repeatedly be generated.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aes_testutils_csrng_kat(void);
#endif

/**
 * Sets up an AES encryption.
 *
 * Starts the encryption operation by loading a key share along with some
 * plain text and transaction data into the AES block.
 * This function is used in tandem with aes_testutils_decrypt_ciphertext.
 *
 * @param transaction The AES transaction settings.
 * @param aes An AES handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aes_testutils_setup_encryption(dif_aes_transaction_t transaction,
                                        dif_aes_t *aes);

/**
 * Reads some produced cipher text and sets up an AES decryption.
 *
 * Starts the decryption operation by loading a key along with some
 * cipher text and transaction data into the AES block. Also checks whether
 * the produced cipher text and decrypted cipher text are correct.
 * This function is used in tandem with aes_testutils_setup_encryption.
 *
 * @param transaction The AES transaction settings used for encryption.
 * @param aes An AES handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t aes_testutils_decrypt_ciphertext(dif_aes_transaction_t transaction,
                                          dif_aes_t *aes);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_AES_TESTUTILS_H_
