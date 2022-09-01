// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_

/**
 * @brief OS-facing API for the OpenTitan cryptography library.
 *
 * NOTE: This API is a work in progress, and the code here only records the
 * current state. It will continue to change until the API design is finalized.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Builds an unblinded key struct from a user (plain) key.
 *
 * @param plain_key Pointer to the user defined plain key
 * @param key_mode Crypto mode for which the key usage is intended
 * @param unblinded_key Generated unblinded key struct
 * @return Result of the build unblinded key operation
 */
crypto_status_t otcrypto_build_unblinded_key(
    crypto_const_uint8_buf_t plain_key, key_mode_t key_mode,
    crypto_unblinded_key_t unblinded_key);

/**
 * Builds a blinded key struct from a plain key.
 *
 * This API takes as input a plain key from the user and masks
 * it using an implantation specific masking with ‘n’ shares and
 * generates a blinded key struct as output.
 *
 * @param plain_key Pointer to the user defined plain key
 * @param key_mode Crypto mode for which the key usage is intended
 * @param blinded_key Generated blinded key struct
 * @return Result of the build blinded key operation
 */
crypto_status_t otcrypto_build_blinded_key(crypto_const_uint8_buf_t plain_key,
                                           key_mode_t key_mode,
                                           crypto_blinded_key_t blinded_key);

/**
 * Exports the blinded key struct to an unblinded key struct.
 *
 * This API takes as input a blinded key masked with ‘n’ shares, and
 * removes the masking and generates an unblinded key struct as output.
 *
 * @param blinded_key Blinded key struct to be unmasked
 * @param unblinded_key Generated unblinded key struct
 * @return Result of the blinded key export operation
 */
crypto_status_t otcrypto_blinded_to_unblinded_key(
    const crypto_blinded_key_t blinded_key,
    crypto_unblinded_key_t unblinded_key);

/**
 * Build a blinded key struct from an unblinded key struct.
 *
 * @param unblinded_key Blinded key struct to be unmasked
 * @param blinded_key Generated (unmasked) unblinded key struct
 * @return Result of unblinded key export operation
 */
crypto_status_t otcrypto_unblinded_to_blinded_key(
    const crypto_unblinded_key unblinded_key, crypto_blinded_key_t blinded_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
