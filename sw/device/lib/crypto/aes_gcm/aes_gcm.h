// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_AES_GCM_AES_GCM_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_AES_GCM_AES_GCM_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/aes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * GHASH operation as defined in NIST SP800-38D, algorithm 2.
 *
 * The input size must be a multiple of the block size.
 *
 * This operation is an internal subcomponent of GCM and should not be used
 * directly except for implementing alternative, customized GCM interfaces
 * (such as using a block cipher other than AES). For other ciphers, the block
 * size must still be 128 bits.
 *
 * @param hash_subkey The hash subkey (a 128-bit cipher block).
 * @param input_len Number of bytes in the input.
 * @param input Pointer to input buffer.
 * @param output Block in which to store the output.
 */
OT_WARN_UNUSED_RESULT
aes_error_t aes_gcm_ghash(const aes_block_t *hash_subkey,
                          const size_t input_len, const uint8_t *input,
                          aes_block_t *output);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_AES_GCM_AES_GCM_H_
