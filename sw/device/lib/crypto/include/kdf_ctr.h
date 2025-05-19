// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_CTR_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_CTR_H_

#include "datatypes.h"

/**
 * @file
 * @brief KDF-CTR operations for the OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Performs KDF-CTR with HMAC as the PRF, according to NIST SP 800-108r1.
 *
 * The caller should allocate and partially populate the `output_key_material`
 * blinded key struct, including populating the key configuration and
 * allocating space for the keyblob. The configuration may not indicate a
 * hardware-backed key and must indicate a symmetric mode. The allocated
 * keyblob length for the output key should be twice the unmasked key length
 * indicated in its key configuration, rounded up to the nearest 32-bit word.
 * The value in the `checksum` field of the blinded key struct will be
 * populated by the key derivation function.
 *
 * @param key_derivation_key Blinded key derivation key.
 * @param label Label string (optional, may be empty).
 * @param context Context string (optional, may be empty).
 * @param[out] output_key_material Blinded output key material.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_ctr_hmac(
    const otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t label,
    const otcrypto_const_byte_buf_t context,
    otcrypto_blinded_key_t *output_key_material);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_CTR_H_
