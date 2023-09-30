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
 * Imports a user provided key to an unblinded key struct.
 *
 * This API takes as input a plain key from the user and writes it to the
 * `unblinded_key.key`.
 *
 * The caller should populate the `unblinded_key.key_mode` and allocate
 * space for the key. The value in the `checksum` field of the unblinded
 * key struct will be populated by the key generation function.
 *
 * @param plain_key Pointer to the user defined plain key.
 * @param[out] unblinded_key Generated unblinded key struct.
 * @return Result of the unblinded key import operation.
 */
crypto_status_t otcrypto_import_unblinded_key(
    const crypto_const_word32_buf_t plain_key,
    crypto_unblinded_key_t *unblinded_key);

/**
 * Imports a user provided masked key in shares, to a blinded key struct.
 *
 * This API takes as input a masked key from the user in two shares, and masks
 * it using an implantation specific masking with ‘n’ shares writing the output
 * to the `blinded_key.keyblob`.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. For non-hardware-backed keys, the keyblob should be twice the
 * length of the user key. For hardware-backed keys, the keyblob length
 * should always be 256 bits and the caller should populate the key blob with
 * their desired key version and salt value. The first 32 bits of the key blob
 * are interpreted in little-endian form as the version, and the remaining
 * 224 bits are concatenated with the one-word key mode to become the salt.
 * This function will return an error if the keyblob length does not match
 * expectations based on the key mode and configuration. The value in the
 * `checksum` field of the blinded key struct will be populated by the key
 * generation function.
 *
 * @param key_share0 Pointer to the 1st share of the user provided key.
 * @param key_share1 Pointer to the 2nd share of the user provided key.
 * @param[out] blinded_key Generated blinded key struct.
 * @return Result of the blinded key import operation.
 */
crypto_status_t otcrypto_import_blinded_key(
    const crypto_const_word32_buf_t key_share0,
    const crypto_const_word32_buf_t key_share1,
    crypto_blinded_key_t *blinded_key);

/**
 * Exports an unblinded key to the user provided key buffer.
 *
 * @param unblinded_key Unblinded key struct to be exported.
 * @param[out] plain_key Pointer to the user provided key buffer.
 * @return Result of the unblinded key export operation.
 */
crypto_status_t otcrypto_export_unblinded_key(
    const crypto_unblinded_key_t unblinded_key, crypto_word32_buf_t *plain_key);

/**
 * Exports a blinded key to the user provided key buffer, in shares.
 *
 * @param blinded_key Blinded key struct to be exported.
 * @param[out] key_share0 Pointer to the 1st share of the user provided key
 * buffer.
 * @param[out] key_share1 Pointer to the 2nd share of the user provided key
 * buffer.
 * @return Result of the blinded key export operation.
 */
crypto_status_t otcrypto_export_blinded_key(
    const crypto_blinded_key_t blinded_key, crypto_word32_buf_t *key_share0,
    crypto_word32_buf_t *key_share1);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_
