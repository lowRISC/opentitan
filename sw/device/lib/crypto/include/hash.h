// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HASH_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HASH_H_

#include "datatypes.h"

/**
 * @file
 * @brief Hash functions for the OpenTitan cryptography library.
 *
 * Supports both SHA2 and SHA3 hash functions, plus the additional Keccak-based
 * hash functions SHAKE and cSHAKE.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Generic hash context.
 *
 * Representation is internal to the hash implementation; initialize
 * with #otcrypto_hash_init.
 */
typedef struct otcrypto_hash_context {
  // Required hash mode.
  otcrypto_hash_mode_t mode;
  // Context for the hash operation.
  uint32_t data[52];
} otcrypto_hash_context_t;

/**
 * Performs the required hash function on the input data.
 *
 * The caller should allocate space for the `digest` buffer and set the `mode`
 * and `len` fields. If the length does not match the mode, an error message
 * will be returned.
 *
 * This function should only be used for fixed-length hash functions (SHA-2 and
 * SHA-3 families). Use `otcrypto_xof_shake` and `otcrypto_xof_cshake` for
 * extendable-output functions.
 *
 * @param input_message Input message to be hashed.
 * @param[out] digest Output digest after hashing the input message.
 * @return Result of the hash operation.
 */
otcrypto_status_t otcrypto_hash(otcrypto_const_byte_buf_t input_message,
                                otcrypto_hash_digest_t digest);

/**
 * Performs the SHAKE extendable output function (XOF) on input data.
 *
 * The caller should allocate space for the `digest` buffer and set the `mode`
 * and `len` fields.  The `mode` parameter must be
 * `kOtcryptoHashXofModeShake128` or `kOtcryptoHashXofModeShake256`; other
 * values will result in errors.
 *
 * @param input_message Input message for extendable output function.
 * @param[out] digest Output from the extendable output function.
 * @return Result of the xof operation.
 */
otcrypto_status_t otcrypto_xof_shake(otcrypto_const_byte_buf_t input_message,
                                     otcrypto_hash_digest_t digest);

/**
 * Performs the CSHAKE extendable output function (XOF) on input data.
 *
 * The `function_name_string` is used by NIST to define functions based on
 * cSHAKE. When no function other than cSHAKE is desired; it can be empty. The
 * `customization_string` is used to define a variant of the cSHAKE function.
 * If no customization is desired it can be empty.
 *
 * The caller should allocate space for the `digest` buffer and set the `mode`
 * and `len` fields. The `mode` parameter must be
 * `kOtcryptoHashXofModeCshake128` or `kOtcryptoHashXofModeCshake256`; other
 * values will result in errors.
 *
 * @param input_message Input message for extendable output function.
 * @param function_name_string NIST Function name string.
 * @param customization_string Customization string for cSHAKE.
 * @param[out] digest Output from the extendable output function.
 * @return Result of the xof operation.
 */
otcrypto_status_t otcrypto_xof_cshake(
    otcrypto_const_byte_buf_t input_message,
    otcrypto_const_byte_buf_t function_name_string,
    otcrypto_const_byte_buf_t customization_string,
    otcrypto_hash_digest_t digest);

/**
 * Performs the INIT operation for a cryptographic hash function.
 *
 * Initializes the generic hash context. The required hash mode is selected
 * through the `hash_mode` parameter. Only `kOtcryptoHashModeSha256`,
 * `kOtcryptoHashModeSha384` and `kOtcryptoHashModeSha512` are supported. Other
 * modes are not supported and an error would be returned.
 *
 * Populates the hash context with the selected hash mode and its digest and
 * block sizes. The structure of hash context and how it populates the required
 * fields are internal to the specific hash implementation.
 *
 * @param ctx Pointer to the generic hash context struct.
 * @param hash_mode Required hash mode.
 * @return Result of the hash init operation.
 */
otcrypto_status_t otcrypto_hash_init(otcrypto_hash_context_t *const ctx,
                                     otcrypto_hash_mode_t hash_mode);

/**
 * Performs the UPDATE operation for a cryptographic hash function.
 *
 * The update operation processes the `input_message` using the selected hash
 * compression function. The intermediate digest is stored in the context
 * `ctx`. Any partial data is stored back in the context and combined with the
 * subsequent bytes.
 *
 * #otcrypto_hash_init should be called before this function.
 *
 * @param ctx Pointer to the generic hash context struct.
 * @param input_message Input message to be hashed.
 * @return Result of the hash update operation.
 */
otcrypto_status_t otcrypto_hash_update(otcrypto_hash_context_t *const ctx,
                                       otcrypto_const_byte_buf_t input_message);

/**
 * Performs the FINAL operation for a cryptographic hash function.
 *
 * The final operation processes the remaining partial blocks, computes the
 * final hash and copies it to the `digest` parameter.
 *
 * #otcrypto_hash_update should be called before this function.
 *
 * The caller should allocate space for the `digest` buffer and set the `mode`
 * and `len` fields. If the `mode` doesn't match the mode of the hash context,
 * the function will return an error.
 *
 * @param ctx Pointer to the generic hash context struct.
 * @param[out] digest Output digest after hashing the input blocks.
 * @return Result of the hash final operation.
 */
otcrypto_status_t otcrypto_hash_final(otcrypto_hash_context_t *const ctx,
                                      otcrypto_hash_digest_t digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_HASH_H_
