// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_H_

#include "sw/device/lib/crypto/include/datatypes.h"

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
 * Enum to define the supported KDF constructions.
 *
 * Values are hardened.
 */
typedef enum kdf_type {
  // KDF construction with HMAC as a PRF.
  kKdfTypeHmac = 0x4f1,
  // KDF construction with KMAC as a PRF.
  kKdfTypeKmac = 0x754,
} kdf_type_t;

/**
 * Performs the key derivation function in counter mode.
 *
 * The required PRF engine for the KDF function is selected using the
 * `kdf_mode` parameter.
 *
 * The caller should allocate and partially populate the `keying_material`
 * blinded key struct, including populating the key configuration and
 * allocating space for the keyblob. The caller should indicate the length of
 * the allocated keyblob; this function will return an error if the keyblob
 * length does not match expectations. For hardware-backed keys, the keyblob
 * length is 0 and the keyblob pointer may be `NULL`. For non-hardware-backed
 * keys, the keyblob should be twice the length of the key. The value in the
 * `checksum` field of the blinded key struct will be populated by this
 * function.
 *
 * @param key_derivation_key Pointer to the blinded key derivation key.
 * @param kdf_mode Required KDF mode, with HMAC or KMAC as a PRF.
 * @param key_mode Crypto mode for which the derived key is intended.
 * @param required_bit_len Required length of the derived key in bits.
 * @param[out] keying_material Pointer to the blinded keying material.
 * @return Result of the key derivation operation.
 */
crypto_status_t otcrypto_kdf_ctr(const crypto_blinded_key_t key_derivation_key,
                                 kdf_type_t kdf_mode, key_mode_t key_mode,
                                 size_t required_bit_len,
                                 crypto_blinded_key_t keying_material);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_KDF_H_
