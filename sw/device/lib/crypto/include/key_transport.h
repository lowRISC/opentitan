// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * @file
 * @brief Key import/export for the OpenTitan cryptography library.
 *
 * These functions allow library users to translate to and from the crypto
 * library's key representations.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Builds an unblinded key struct from a user (plain) key.
 *
 * @param plain_key Pointer to the user defined plain key.
 * @param key_mode Crypto mode for which the key usage is intended.
 * @param[out] unblinded_key Generated unblinded key struct.
 * @return Result of the build unblinded key operation.
 */
crypto_status_t otcrypto_build_unblinded_key(
    crypto_const_byte_buf_t plain_key, key_mode_t key_mode,
    crypto_unblinded_key_t unblinded_key);

/**
 * Builds a blinded key struct from a plain key.
 *
 * This API takes as input a plain key from the user and masks it using an
 * implantation specific masking with ‘n’ shares writing the output to
 * `blinded_key.keyblob`.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. For hardware-backed keys, the keyblob length is 0 and the
 * keyblob pointer may be `NULL`. For non-hardware-backed keys, the keyblob
 * should be twice the length of the key. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 *
 * @param plain_key Pointer to the user defined plain key.
 * @param[out] blinded_key Destination blinded key struct.
 * @return Result of the build blinded key operation.
 */
crypto_status_t otcrypto_build_blinded_key(crypto_const_byte_buf_t plain_key,
                                           crypto_blinded_key_t blinded_key);

/**
 * Exports the blinded key struct to an unblinded key struct.
 *
 * This API takes as input a blinded key masked with ‘n’ shares, and
 * removes the masking and generates an unblinded key struct as output.
 *
 * @param blinded_key Blinded key struct to be unmasked.
 * @param[out] unblinded_key Generated unblinded key struct.
 * @return Result of the blinded key export operation.
 */
crypto_status_t otcrypto_blinded_to_unblinded_key(
    const crypto_blinded_key_t blinded_key,
    crypto_unblinded_key_t unblinded_key);

/**
 * Build a blinded key struct from an unblinded key struct.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. For hardware-backed keys, the keyblob length is 0 and the
 * keyblob pointer may be `NULL`. For non-hardware-backed keys, the keyblob
 * should be twice the length of the key. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 *
 * @param unblinded_key Unblinded key struct to be masked.
 * @param[out] blinded_key Generated (masked) blinded key struct.
 * @return Result of blinding operation.
 */
crypto_status_t otcrypto_unblinded_to_blinded_key(
    const crypto_unblinded_key_t unblinded_key,
    crypto_blinded_key_t blinded_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_
