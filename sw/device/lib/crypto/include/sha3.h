// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA3_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA3_H_

#include "datatypes.h"

/**
 * @file
 * @brief Keccak-based hash functions for the OpenTitan cryptography library.
 *
 * Supports SHA3, SHAKE, and cSHAKE operations.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * One-shot SHA3-224 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 224
 * bits (= 7 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_224(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA3-256 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 256
 * bits (= 8 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_256(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA3-384 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 384
 * bits (= 12 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_384(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHA3-512 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * accordingly. The function will return an error if the length is not 512
 * bits (= 16 32-bit words). The `digest.mode` field is set by this function and
 * may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_sha3_512(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHAKE128 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake128(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot SHAKE256 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * @param message Input message.
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_shake256(otcrypto_const_byte_buf_t message,
                                    otcrypto_hash_digest_t *digest);

/**
 * One-shot cSHAKE128 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * The function name and customization string parameters are defined in NIST
 * SP800-185; please refer to that document for guidance on their usage.
 *
 * @param message Input message.
 * @param function_name_string Function name parameter (may be empty).
 * @param customization_string Customization parameter (may be empty).
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake128(
    otcrypto_const_byte_buf_t message,
    otcrypto_const_byte_buf_t function_name_string,
    otcrypto_const_byte_buf_t customization_string,
    otcrypto_hash_digest_t *digest);

/**
 * One-shot cSHAKE256 hash computation.
 *
 * The caller should allocate space for the digest and set `digest.len`
 * according to their desired output length. The `digest.mode` field is set by
 * this function and may be uninitialized.
 *
 * The function name and customization string parameters are defined in NIST
 * SP800-185; please refer to that document for guidance on their usage.
 *
 * @param message Input message.
 * @param function_name_string Function name parameter (may be empty).
 * @param customization_string Customization parameter (may be empty).
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_cshake256(
    otcrypto_const_byte_buf_t message,
    otcrypto_const_byte_buf_t function_name_string,
    otcrypto_const_byte_buf_t customization_string,
    otcrypto_hash_digest_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_SHA3_H_
