// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_GHASH_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_GHASH_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of a GHASH cipher block (128 bits) in bytes.
   */
  kGhashBlockNumBytes = 128 / 8,
  /**
   * Size of a GHASH cipher block (128 bits) in words.
   */
  kGhashBlockNumWords = kGhashBlockNumBytes / sizeof(uint32_t),
};

/**
 * A type that holds a single cipher block.
 */
typedef struct ghash_block {
  uint32_t data[kGhashBlockNumWords];
} ghash_block_t;

typedef struct ghash_context {
  /**
   * Precomputed product table for the hash subkey.
   */
  ghash_block_t tbl[16];
  /**
   * Cipher block representing the current GHASH state.
   */
  ghash_block_t state;
} ghash_context_t;

/**
 * Precompute hash subkey information for GHASH.
 *
 * This routine will precompute a product table for the hash subkey for the
 * GHASH context. It will not set the state to 0; call `ghash_init` afterwards.
 *
 * This operation should only be called once per key, and afterwards the
 * context object can be used for multiple separate GHASH operations with that
 * key. The reason for separating this and `ghash_init` into two functions is
 * that computing the product table is computationally expensive, and some GCM
 * computations need to compute more than one separate GHASH operation.
 *
 * @param hash_subkey Subkey for the GHASH operation (`kGhashBlockNumWords`
 * words).
 * @param[out] ctx Context object with product table populated.
 */
void ghash_init_subkey(const uint32_t *hash_subkey, ghash_context_t *ctx);

/**
 * Start a GHASH operation.
 *
 * This routine will initialize the GHASH state within the context object to
 * zero. It will not precompute the key product table; call `ghash_init_subkey`
 * first.
 *
 * @param[out] ctx Context object with GHASH state reset to zero.
 */
void ghash_init(ghash_context_t *ctx);

/**
 * Given a partial GHASH block and some new input, process full blocks.
 *
 * Concatenates the new input to the partial data and processes any full blocks
 * with GHASH. Updates the partial block with the new, leftover partial data
 * after processing the new input.
 *
 * The partial block may be empty, but should never be full; `partial_len`
 * should always be less than `kGhashBlockNumBytes`.
 *
 * @param ctx Context object.
 * @param partial_len Length of the partial block.
 * @param partial Partial GHASH block.
 * @param input_len Length of the input data in bytes.
 * @param input Input data.
 */
void ghash_process_full_blocks(ghash_context_t *ctx, size_t partial_len,
                               ghash_block_t *partial, size_t input_len,
                               const uint8_t *input);
/**
 * Update the state of a GHASH operation.
 *
 * Pads the input with 0s on the right-hand side if needed so that the input
 * size is a multiple of the block size. Given a state representing GHASH(A)
 * and a new input B, this function will return a state representing:
 *   GHASH(A || B || <padding for B>)
 *
 * Initialize the context object with `ghash_init_subkey` and `ghash_init`
 * before calling this function.
 *
 * @param ctx Context object.
 * @param input_len Number of bytes in the input.
 * @param input Pointer to input buffer.
 */
void ghash_update(ghash_context_t *ctx, size_t input_len, const uint8_t *input);

/**
 * Update the state of a GHASH operation.
 *
 * Pads the input with 0s on the right-hand side if needed so that the input
 * size is a multiple of the block size. Given a state representing GHASH(A)
 * and a new input B, this function will return a state representing:
 *   GHASH(A || B || <padding for B>)
 *
 * Initialize the context object with `ghash_init_subkey` and `ghash_init`
 * before calling this function.
 *
 * The caller must ensure that at least `kGhashBlockNumWords` words are
 * allocated in the `result` buffer.
 *
 * @param ctx Context object.
 * @param[out] result Buffer in which to write the GHASH result block
 */
void ghash_final(ghash_context_t *ctx, uint32_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_GHASH_H_
