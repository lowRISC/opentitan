// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_

#include "datatypes.h"

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
 * Generates a new, random symmetric key.
 *
 * Use this only for symmetric algorithms (e.g. AES, HMAC, KMAC). Asymmetric
 * algorithms (e.g. ECDSA, RSA) have their own specialized key-generation
 * routines. Cannot be used for hardware-backed keys; use
 * `otcrypto_hw_backed_key` instead to generate these.
 *
 * The caller should allocate space for the keyblob and populate the blinded
 * key struct with the length of the keyblob, the pointer to the keyblob
 * buffer, and the key configuration. The value in the `checksum` field of
 * the blinded key struct will be populated by the key generation function.
 * The keyblob should be twice the length of the unblinded key.  This function
 * will return an error if the keyblob length does not match expectations based
 * on the key mode and configuration.
 *
 * The keyblob should be twice the length of the key. The caller only needs to
 * allocate the keyblob, not populate it.
 *
 * The personalization string may empty, and may be up to 48 bytes long; any
 * longer will result in an error. It is passed as an extra seed input to the
 * DRBG, in addition to the hardware TRNG.
 *
 * @param perso_string Optional personalization string to be passed to DRBG.
 * @param[out] key Destination blinded key struct.
 * @return The result of the operation.
 */
otcrypto_status_t otcrypto_symmetric_keygen(
    otcrypto_const_byte_buf_t perso_string, otcrypto_blinded_key_t *key);

/**
 * Creates a handle for a hardware-backed key.
 *
 * This routine may be used for both symmetric and asymmetric algorithms, since
 * conceptually it only creates some data that the key manager can use to
 * generate key material at the time of use. However, not all algorithms are
 * suitable for hardware-backed keys (for example, RSA is not suitable), so
 * some choices of algorithm may result in errors.
 *
 * The caller should partially populate the blinded key struct; they should set
 * the full key configuration and the keyblob length (always 32 bytes), and
 * then allocate 32 bytes of space for the keyblob and set the keyblob pointer.
 *
 * This function will populate the `checksum` field and copy the salt/version
 * data into the keyblob buffer in the specific order that the rest of
 * cryptolib expects.
 *
 * @param version Key version.
 * @param salt Key salt (diversification data for KDF).
 * @param[out] key Destination blinded key struct.
 * @return The result of the operation.
 */
otcrypto_status_t otcrypto_hw_backed_key(uint32_t version,
                                         const uint32_t salt[7],
                                         otcrypto_blinded_key_t *key);

/**
 * Creates a blinded key struct from masked key material.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The keyblob should be twice the length of the user key.
 * Hardware-backed and asymmetric (ECC or RSA) keys cannot be imported this
 * way. For asymmetric keys, use algorithm-specific key construction methods.
 *
 * This function will copy the data from the shares into the keyblob; it is
 * safe to free `key_share0` and `key_share1` after this call.
 *
 * @param key_share0 First share of the user provided key.
 * @param key_share1 Second share of the user provided key.
 * @param[out] blinded_key Generated blinded key struct.
 * @return Result of the blinded key import operation.
 */
otcrypto_status_t otcrypto_import_blinded_key(
    const otcrypto_const_word32_buf_t key_share0,
    const otcrypto_const_word32_buf_t key_share1,
    otcrypto_blinded_key_t *blinded_key);

/**
 * Exports a blinded key to the user provided key buffer, in shares.
 *
 * This function will copy data from the keyblob into the shares; after the
 * call, it is safe to free the blinded key and the data pointed to by
 * `blinded_key.keyblob`.
 *
 * Hardware-backed, non-exportable, and asymmetric (ECC or RSA) keys cannot be
 * exported this way. For asymmetric keys, use an algorithm-specific funtion.
 *
 * @param blinded_key Blinded key struct to be exported.
 * @param[out] key_share0 First share of the blinded key.
 * @param[out] key_share1 Second share of the blinded key.
 * @return Result of the blinded key export operation.
 */
otcrypto_status_t otcrypto_export_blinded_key(
    const otcrypto_blinded_key_t blinded_key, otcrypto_word32_buf_t key_share0,
    otcrypto_word32_buf_t key_share1);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_
