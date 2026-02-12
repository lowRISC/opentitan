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
OT_WARN_UNUSED_RESULT
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
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_hw_backed_key(uint32_t version,
                                         const uint32_t salt[7],
                                         otcrypto_blinded_key_t *key);

/**
 * Returns the length that the blinded key will have once wrapped.
 *
 * @param config Key configuration.
 * @param[out] wrapped_num_words Number of 32b words for the wrapped key.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_wrapped_key_len(const otcrypto_key_config_t config,
                                           size_t *wrapped_num_words);

/**
 * Wraps (encrypts) a secret key.
 *
 * The key wrap function uses AES-KWP (key wrapping with padding), an
 * authenticated encryption mode designed for encrypting key material.
 *
 * The caller should allocate space for the `wrapped_key` buffer according to
 * `otcrypto_wrapped_key_len`, and set the length of expected output in the
 * `len` field of `wrapped_key`. If the user-set length and the output length
 * do not match, an error message will be returned.
 *
 * The blinded key struct to wrap must be 32-bit aligned.
 *
 * @param key_to_wrap Blinded key that will be encrypted.
 * @param key_kek AES-KWP key used to encrypt `key_to_wrap`.
 * @param[out] wrapped_key Encrypted key data.
 * @return Result of the wrap operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_key_wrap(const otcrypto_blinded_key_t *key_to_wrap,
                                    const otcrypto_blinded_key_t *key_kek,
                                    otcrypto_word32_buf_t wrapped_key);

/**
 * Unwraps (decrypts) a secret key.
 *
 * The key unwrap function uses AES-KWP (key wrapping with padding), an
 * authenticated encryption mode designed for encrypting key material.
 *
 * The caller must allocate space for the keyblob and set the keyblob-length
 * and keyblob fields in `unwrapped_key` accordingly. If there is not enough
 * space in the keyblob, this function will return an error. Too much space in
 * the keyblob is okay; this function will write to the first part of the
 * keyblob buffer and set the keyblob length field to the correct exact value
 * for the unwrapped key, at which point it is safe to check the new length and
 * free the remaining keyblob memory. It is always safe to allocate a keyblob
 * the same size as the wrapped key; this will always be enough space by
 * definition.
 *
 * The caller does not need to populate the blinded key configuration, since
 * this information is encrypted along with the key.  However, the caller may
 * want to check that the configuration matches expectations.
 *
 * An OK status from this function does NOT necessarily mean that unwrapping
 * succeeded; the caller must check both the returned status and the `success`
 * parameter before reading the unwrapped key.
 *
 * @param wrapped_key Encrypted key data.
 * @param key_kek AES-KWP key used to decrypt `wrapped_key`.
 * @param[out] success Whether the wrapped key was valid.
 * @param[out] unwrapped_key Decrypted key data.
 * @return Result of the aes-kwp unwrap operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_key_unwrap(otcrypto_const_word32_buf_t wrapped_key,
                                      const otcrypto_blinded_key_t *key_kek,
                                      hardened_bool_t *success,
                                      otcrypto_blinded_key_t *unwrapped_key);

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
OT_WARN_UNUSED_RESULT
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
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_export_blinded_key(
    const otcrypto_blinded_key_t *blinded_key, otcrypto_word32_buf_t key_share0,
    otcrypto_word32_buf_t key_share1);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KEY_TRANSPORT_H_
