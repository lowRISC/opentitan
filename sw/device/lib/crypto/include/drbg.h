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
 * Initializes the DRBG and the context for DRBG. Gets the required entropy
 * input automatically from the entropy source.
 *
 * The personalization string may empty, and may be up to 48 bytes long; any
 * longer will result in an error.
 *
 * @param perso_string Pointer to personalization bitstring.
 * @return Result of the DRBG instantiate operation.
 */
crypto_status_t otcrypto_drbg_instantiate(crypto_const_byte_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with fresh entropy that is automatically fetched from the
 * entropy source and updates the working state parameters.
 *
 * @param additional_input Pointer to the additional input for DRBG.
 * @return Result of the DRBG reseed operation.
 */
crypto_status_t otcrypto_drbg_reseed(crypto_const_byte_buf_t additional_input);

/**
 * Instantiates the DRBG system.
 *
 * Initializes DRBG and the DRBG context. Gets the required entropy input from
 * the user through the `entropy` parameter. Calling this function breaks FIPS
 * compliance until the DRBG is uninstantiated.
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
    crypto_const_byte_buf_t entropy, crypto_const_byte_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with entropy input from the user through the `entropy`
 * parameter and updates the working state parameters. Calling this function
 * breaks FIPS compliance until the DRBG is uninstantiated.
 *
 * @param entropy Pointer to the user defined entropy value.
 * @param additional_input Pointer to the additional input for DRBG.
 * @return Result of the manual DRBG reseed operation.
 */
crypto_status_t otcrypto_drbg_manual_reseed(
    crypto_const_byte_buf_t entropy, crypto_const_byte_buf_t additional_input);

/**
 * DRBG function for generating random bits.
 *
 * This function checks the hardware flags for FIPS compatibility of the
 * generated bits, so it will fail after `otcrypto_drbg_manual_instantiate` or
 * `otcrypto_drbg_manual_reseed`.
 *
 * The caller should allocate space for the `drbg_output` buffer and set the
 * length of expected output in the `len` field.
 *
 * The output is generated in 16-byte blocks; if `drbg_output->len` is not a
 * multiple of 4, some output from the hardware will be discarded. This detail
 * may be important for known-answer tests.
 *
 * @param additional_input Pointer to the additional data.
 * @param[out] drbg_output Pointer to the generated pseudo random bits.
 * @return Result of the DRBG generate operation.
 */
crypto_status_t otcrypto_drbg_generate(crypto_const_byte_buf_t additional_input,
                                       crypto_word32_buf_t *drbg_output);

/**
 * DRBG function for generating random bits.
 *
 * This function does NOT check the hardware flags for FIPS compatibility of the
 * generated bits, so it may be called after `otcrypto_drbg_manual_instantiate`
 * or `otcrypto_drbg_manual_reseed`.
 *
 * The caller should allocate space for the `drbg_output` buffer and set the
 * length of expected output in the `len` field.
 *
 * The output is generated in 16-byte blocks; if `drbg_output->len` is not a
 * multiple of 4, some output from the hardware will be discarded. This detail
 * may be important for known-answer tests.
 *
 * @param additional_input Pointer to the additional data.
 * @param[out] drbg_output Pointer to the generated pseudo random bits.
 * @return Result of the DRBG generate operation.
 */
crypto_status_t otcrypto_drbg_manual_generate(
    crypto_const_byte_buf_t additional_input, crypto_word32_buf_t *drbg_output);

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
