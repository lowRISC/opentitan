// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_H_

#include "datatypes.h"
#include "mac.h"

/**
 * @file
 * @brief Key derivation functions for the OpenTitan cryptography library.
 *
 * Includes HMAC- and KMAC-based KDFs.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Performs the key derivation function in counter mode wtih HMAC according to
 * NIST SP 800-108r1.
 *
 * The supported PRF engine for the KDF function is HMAC (since KMAC does not
 * use the counter mode).
 *
 * The caller should allocate and partially populate the `keying_material`
 * blinded key struct, including populating the key configuration and
 * allocating space for the keyblob. The caller should indicate the length of
 * the allocated keyblob; this function will return an error if the keyblob
 * length does not match expectations. For hardware-backed keys, the keyblob
 * expectations. If the key is hardware-backed, the caller should pass a fully
 * populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`. For non-hardware-backed keys, the keyblob should
 * be twice the length of the key. The value in the `checksum` field of the
 * blinded key struct will be populated by this function.
 *
 * @param key_derivation_key Blinded key derivation key.
 * @param kdf_label Label string according to SP 800-108r1.
 * @param kdf_context Context string according to SP 800-108r1.
 * @param required_byte_len Required length of the derived key in bytes.
 * @param[out] keying_material Pointer to the blinded keying material to be
 * populated by this function.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_hmac_ctr(
    const otcrypto_blinded_key_t key_derivation_key,
    const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material);

/**
 * Performs the key derivation function with single KMAC invocation according to
 * NIST SP 800-108r1.
 *
 * This function initially validates the `key_derivation_key` struct, by
 * checking for NULL pointers, checking whether key length and its
 * keyblob_length match each other, verifying its checksum etc. Moreover, its
 * `hw_backed` field is used to determine whether the derivation key comes from
 * Keymgr. In that case, this function requests Keymgr to generate the key
 * according to diversification values passed in keyblob.
 * (see `keyblob_buffer_to_keymgr_diversification` function in `keyblob.h`).
 * For non-hardware-backed keys, the keyblob should be twice the length of the
 * key.
 *
 * `kmac_mode` input argument is used to decide whether KMAC128 or KMAC256 is
 * used and it is also checked against `key_mode` from `key_derivation_key`.
 *
 * The produced key is returned in the `keying_material` blinded key struct.
 * The caller should allocate and partially populate `keying_material`,
 * including populating the key configuration and allocating space for the
 * keyblob. The key length is also checked against `required_byte_len`. The
 * value in the `checksum` field of the blinded key struct will be populated
 * by this function. The use case where `keying_material` needs to be hw-backed
 * is not supported by this function, hence `hw_backed` must be set tofalse.
 * See `otcrypto_hw_backed_key` from `key_transport` for that specific use case.
 *
 * Note that it is the responsibility of the user of `keying_material` to
 * further validate the key configuration. While populating the key, this
 * function ignores `exportable`, `key_mode`, and `security_level` fields
 * therefore the users must validate their `keying_material` config before use.
 *
 * @param key_derivation_key Blinded key derivation key.
 * @param kmac_mode Either KMAC128 or KMAC256 as PRF.
 * @param kdf_label Label string according to SP 800-108r1.
 * @param kdf_context Context string according to SP 800-108r1.
 * @param required_byte_len Required length of the derived key in bytes.
 * @param[out] keying_material Pointer to the blinded keying material to be
 * populated by this function.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_kmac(
    const otcrypto_blinded_key_t key_derivation_key,
    otcrypto_kmac_mode_t kmac_mode, const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material);

/**
 * Performs HKDF in one shot, both expand and extract stages.
 *
 * HKDF is defined in IETF RFC 5869 and is based on HMAC. The HMAC hash
 * function is determined by the mode of the key derivation key, e.g. the key
 * mode `kOtcryptoKeyModeHmacSha256` results in HMAC with SHA-256. The key mode
 * for the output pseudo-random key (PRK) should match the key mode for the
 * input key derivation key.
 *
 * The caller should allocate and partially populate the `prk` blinded key
 * struct, including populating the key configuration and allocating space for
 * the keyblob. The PRK configuration may not indicate a hardware-backed key.
 * The allocated keyblob length should be twice the length of the hash function
 * digest length.
 * The caller should allocate and partially populate the `derived_key` blinded
 * key struct, including populating the key configuration and allocating space
 * for the keyblob. The key configuration may not indicate a hardware-backed
 * key. The allocated keyblob length should be twice the key length indicated
 * in the key configuration, and this key length must not be longer than
 * 255*<length of hash digest> as per the RFC.
 *
 * @param key_derivation_key Blinded key derivation key.
 * @param salt Salt value (optional, may be empty).
 * @param info Context-specific string (optional, may be empty).
 * @param[out] derived_key Derived keying material.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_hkdf(
    const otcrypto_blinded_key_t key_derivation_key,
    otcrypto_const_byte_buf_t salt, otcrypto_const_byte_buf_t info,
    otcrypto_blinded_key_t *derived_key);

/**
 * Performs the "extract" step of HKDF.
 *
 * HKDF is defined in IETF RFC 5869 and is based on HMAC. The HMAC hash
 * function is determined by the mode of the key derivation key,  e.g. the key
 * mode `kOtcryptoKeyModeHmacSha256` results in HMAC with SHA-256. The key mode
 * for the output pseudo-random key (PRK) should match the key mode for the
 * input key derivation key.
 *
 * The resulting pseudo-random key is then input for the "expand" step of HKDF.
 * The length of PRK is the same as the digest length for the specified hash
 * function (e.g. 256 bits for SHA-256).
 *
 * The caller should allocate and partially populate the `prk` blinded key
 * struct, including populating the key configuration and allocating space for
 * the keyblob. The PRK configuration may not indicate a hardware-backed key.
 * The allocated keyblob length should be twice the length of the hash function
 * digest length.
 *
 * @param ikm Blinded input key material.
 * @param salt Salt value (optional, may be empty).
 * @param[out] prk Extracted pseudo-random key.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_hkdf_extract(const otcrypto_blinded_key_t ikm,
                                            otcrypto_const_byte_buf_t salt,
                                            otcrypto_blinded_key_t *prk);

/**
 * Performs the "expand" step of HKDF.
 *
 * HKDF is defined in IETF RFC 5869 and is based on HMAC. The HMAC hash
 * function is inferred from the key mode of the pseudo-random key (PRK).
 *
 * The input pseudo-random key should be generated from the "extract" step of
 * HKDF. Its length should always be the same as the digest length of the hash
 * function.
 *
 * The caller should allocate and partially populate the `okm` blinded key
 * struct, including populating the key configuration and allocating space for
 * the keyblob. The key configuration may not indicate a hardware-backed key.
 * The allocated keyblob length should be twice the key length indicated in the
 * key configuration, and this key length must not be longer than 255*<length
 * of hash digest> as per the RFC.
 *
 * @param prk Pseudo-random key from HKDF-extract.
 * @param info Context-specific string (optional).
 * @param[out] okm Blinded output key material.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_hkdf_expand(const otcrypto_blinded_key_t prk,
                                           otcrypto_const_byte_buf_t info,
                                           otcrypto_blinded_key_t *okm);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_H_
