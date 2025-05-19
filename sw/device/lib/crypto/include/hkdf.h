// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HKDF_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HKDF_H_

#include "datatypes.h"

/**
 * @file
 * @brief HKDF operations for the OpenTitan cryptography library.
 *
 * Implements the HMAC-based extract-and-expand key derivation function
 * specified in IETF RFC 5869.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Performs HKDF (IETF RFC 5869) in one shot, both expand and extract stages.
 *
 * The hash mode for the underlying HMAC is determined by the mode of the input
 * key material, e.g. the key mode `kOtcryptoKeyModeHmacSha256` results in HMAC
 * with SHA-256.
 *
 * The caller should allocate and partially populate the `okm` blinded key
 * struct, including populating the key configuration and allocating space for
 * the keyblob. The configuration may not indicate a hardware-backed key and
 * must indicate a symmetric mode. The allocated keyblob length for the output
 * key should be twice the unmasked key length indicated in its key
 * configuration, rounded up to the nearest 32-bit word. This unmasked key
 * length must not be longer than 255*<length of digest for the chosen hash
 * mode>, as per the RFC. The value in the `checksum` field of the blinded key
 * struct will be populated by the key derivation function.
 *
 * @param ikm Blinded input key material.
 * @param salt Salt value (optional, may be empty).
 * @param info Context-specific string (optional, may be empty).
 * @param[out] okm Blinded output keying material.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_hkdf(const otcrypto_blinded_key_t *ikm,
                                otcrypto_const_byte_buf_t salt,
                                otcrypto_const_byte_buf_t info,
                                otcrypto_blinded_key_t *okm);

/**
 * Performs the "extract" step of HKDF (IETF RFC 5869).
 *
 * The hash mode for the underlying HMAC is determined by the mode of the input
 * key material, e.g. the key mode `kOtcryptoKeyModeHmacSha256` results in HMAC
 * with SHA-256.
 *
 * The caller should allocate and partially populate the `prk` blinded key
 * struct, including populating the key configuration and allocating space for
 * the keyblob. The configuration may not indicate a hardware-backed key, and
 * the mode should be the same HMAC mode as the input keying material. The
 * allocated keyblob length should be twice the hash function digest length for
 * the chosen hash mode (e.g. 512 bits for SHA-256).
 *
 * @param ikm Blinded input key material.
 * @param salt Salt value (optional, may be empty).
 * @param[out] prk Extracted pseudo-random key.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_hkdf_extract(const otcrypto_blinded_key_t *ikm,
                                        otcrypto_const_byte_buf_t salt,
                                        otcrypto_blinded_key_t *prk);

/**
 * Performs the "expand" step of HKDF (IETF RFC 5869).
 *
 * The hash mode for the underlying HMAC is determined by the mode of the
 * pseudo-random key, e.g. the key mode `kOtcryptoKeyModeHmacSha256` results in
 * HMAC with SHA-256.
 *
 * See `otcrypto_hkdf` for the requirements on `okm`.
 *
 * @param prk Pseudo-random key from HKDF-extract.
 * @param info Context-specific string (optional).
 * @param[out] okm Blinded output key material.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_hkdf_expand(const otcrypto_blinded_key_t *prk,
                                       otcrypto_const_byte_buf_t info,
                                       otcrypto_blinded_key_t *okm);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HKDF_H_
