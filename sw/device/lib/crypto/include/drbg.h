// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DRBG_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DRBG_H_

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * @file
 * @brief DRBG for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Instantiates the DRBG system.
 *
 * Initializes the DRBG and the context for DRBG. Gets the required
 * entropy input automatically from the entropy source.
 *
 * @param perso_string Pointer to personalization bitstring.
 * @return Result of the DRBG instantiate operation.
 */
crypto_status_t otcrypto_drbg_instantiate(crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with fresh entropy that is automatically fetched
 * from the entropy source and updates the working state parameters.
 *
 * @param additional_input Pointer to the additional input for DRBG.
 * @return Result of the DRBG reseed operation.
 */
crypto_status_t otcrypto_drbg_reseed(crypto_uint8_buf_t additional_input);

/**
 * Instantiates the DRBG system.
 *
 * Initializes DRBG and the DRBG context. Gets the required entropy
 * input from the user through the `entropy` parameter.
 *
 * The entropy input must be exactly 384 bits long (48 bytes). The
 * personalization string must not be longer than the entropy input, and may be
 * empty.
 *
 * @param entropy Pointer to the user defined entropy value.
 * @param personalization_string Pointer to personalization bitstring.
 * @return Result of the DRBG manual instantiation.
 */
crypto_status_t otcrypto_drbg_manual_instantiate(
    crypto_uint8_buf_t entropy, crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with entropy input from the user through `entropy`
 * parameter and updates the working state parameters.
 *
 * @param entropy Pointer to the user defined entropy value.
 * @param additional_input Pointer to the additional input for DRBG.
 * @return Result of the manual DRBG reseed operation.
 */
crypto_status_t otcrypto_drbg_manual_reseed(
    crypto_uint8_buf_t entropy, crypto_uint8_buf_t additional_input);

/**
 * DRBG function for generating random bits.
 *
 * Used to generate pseudo random bits after DRBG instantiation or
 * DRBG reseeding.
 *
 * The caller should allocate space for the `drbg_output` buffer,
 * (of length `output_len`), and set the length of expected
 * output in the `len` field of `drbg_output`. If the user-set length
 * and the output length does not match, an error message will be
 * returned.
 *
 * The output is generated in 16-byte blocks; if `output_len` is not a multiple
 * of 16, some output from the hardware will be discarded. This detail may be
 * important for known-answer tests.
 *
 * @param additional_input Pointer to the additional data.
 * @param output_len Required len of pseudorandom output, in bytes.
 * @param[out] drbg_output Pointer to the generated pseudo random bits.
 * @return Result of the DRBG generate operation.
 */
crypto_status_t otcrypto_drbg_generate(crypto_uint8_buf_t additional_input,
                                       size_t output_len,
                                       crypto_uint8_buf_t *drbg_output);

/**
 * Uninstantiates DRBG and clears the context.
 *
 * @return Result of the DRBG uninstantiate operation.
 */
crypto_status_t otcrypto_drbg_uninstantiate(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DRBG_H_
