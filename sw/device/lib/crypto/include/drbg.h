// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DRBG_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DRBG_H_

/**
 * @file
 * @brief DRBG for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * DRBG state.
 *
 * Representation is internal to the drbg implementation; initialize
 * with #otcrypto_drbg_instantiate or
 * #otcrypto_drbg_manual_instantiate.
 *
 * Note: The drbg_state_t struct along with V and K, should include:
 * drbg_entropy_mode: To indicate the entropy mode used. Also used to
 * disallow mixing of auto entropy and manual entropy DRBG operations.
 * reseed_counter: To indicate the number of requests for pseudorandom
 * bits since instantiation or reseeding.
 * security_strength: To indicate security strength of the DRBG
 * instantiation.
 * prediction_resistance_flag: To indicate if prediction resistance is
 * required.
 * drbg_mechanism: To indicate if CTR_DRBG or HMAC_DRBG is used for
 * the DRBG instantiation.
 */
typedef struct drbg_state drbg_state_t;

/**
 * Instantiates the DRBG system.
 *
 * Initializes the DRBG and the context for DRBG. Gets the required
 * entropy input automatically from the entropy source.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param nonce Pointer to the nonce bit-string
 * @param perso_string Pointer to personalization bitstring
 * @return Result of the DRBG instantiate operation
 */
crypto_status_t otcrypto_drbg_instantiate(drbg_state_t *drbg_state,
                                          crypto_uint8_buf_t nonce,
                                          crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with fresh entropy that is automatically fetched
 * from the entropy source and updates the working state parameters.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param additional_input Pointer to the additional input for DRBG
 * @return Result of the DRBG reseed operation
 */
crypto_status_t otcrypto_drbg_reseed(drbg_state_t *drbg_state,
                                     crypto_uint8_buf_t additional_input);

/**
 * Instantiates the DRBG system.
 *
 * Initializes DRBG and the DRBG context. Gets the required entropy
 * input from the user through the `entropy` parameter.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param entropy Pointer to the user defined entropy value
 * @param nonce Pointer to the nonce bit-string
 * @param personalization_string Pointer to personalization bitstring
 * @return Result of the DRBG manual instantiation
 */
crypto_status_t otcrypto_drbg_manual_instantiate(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t nonce, crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with entropy input from the user through `entropy`
 * parameter and updates the working state parameters.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param entropy Pointer to the user defined entropy value
 * @param additional_input Pointer to the additional input for DRBG
 * @return Result of the manual DRBG reseed operation
 */
crypto_status_t otcrypto_drbg_manual_reseed(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t additional_input);

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
 * @param drbg_state Pointer to the DRBG working state
 * @param additional_input Pointer to the additional data
 * @param output_len Required len of pseudorandom output, in bytes
 * @param drbg_output Pointer to the generated pseudo random bits
 * @return Result of the DRBG generate operation
 */
crypto_status_t otcrypto_drbg_generate(drbg_state_t *drbg_state,
                                       crypto_uint8_buf_t additional_input,
                                       size_t output_len,
                                       crypto_uint8_buf_t *drbg_output);

/**
 * Uninstantiates DRBG and clears the context.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @return Result of the DRBG uninstantiate operation
 */
crypto_status_t otcrypto_drbg_uninstantiate(drbg_state_t *drbg_state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DRBG_H_
