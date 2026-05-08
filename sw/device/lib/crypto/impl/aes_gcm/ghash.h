// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_GHASH_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_GHASH_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/include/datatypes.h"

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
   * Precomputed product table for the hash subkey share 0.
   */
  ghash_block_t tbl0[16];
  /**
   * Precomputed product table for the hash subkey share 1.
   */
  ghash_block_t tbl1[16];
  /**
   * Cipher block representing the current GHASH state for share 0.
   */
  ghash_block_t state0;
  /**
   * Cipher block representing the current GHASH state for share 1.
   */
  ghash_block_t state1;
  /**
   * Precomputed correction term (S0 * (H0+1)) for state share 0.
   */
  ghash_block_t correction_term0;
  /**
   * Precomputed correction term (S0 * H1) for state share 1.
   */
  ghash_block_t correction_term1;
  /**
   * Precomputed initial correction term (S1 * H1) for state share 1.
   */
  ghash_block_t correction_term1_init;
  /**
   * Encrypted initial counter block share 0.
   */
  ghash_block_t enc_initial_counter_block0;
  /**
   * Encrypted initial counter block share 1.
   */
  ghash_block_t enc_initial_counter_block1;
  /**
   * Number of processed ghash blocks.
   */
  size_t ghash_block_cnt;
  /**
   * Checksum of the structure.
   */
  uint32_t checksum;
} ghash_context_t;

/**
 * Compute the checksum of a ghash context.
 *
 * Call this routine after creating or modifying the structure.
 *
 * @param ghash_ctx ghash context.
 * @returns Checksum value.
 */
uint32_t ghash_context_integrity_checksum(const ghash_context_t *ghash_ctx);

/**
 * Perform an integrity check on the ghash context.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param ghash_ctx ghash context.
 * @returns Whether the integrity check passed.
 */
hardened_bool_t ghash_context_integrity_checksum_check(
    const ghash_context_t *ghash_ctx);

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
 * @param[out] tbl The populated product table.
 */
status_t ghash_init_subkey(const uint32_t *hash_subkey, ghash_block_t *tbl);

/**
 * Start a GHASH operation.
 *
 * This routine will initialize the GHASH state within the context object to
 * zero. It will not precompute the key product table; call `ghash_init_subkey`
 * first.
 *
 * @param[out] ctx Context object with GHASH state reset to zero.
 */
status_t ghash_init(ghash_context_t *ctx);

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
status_t ghash_process_full_blocks(ghash_context_t *ctx, size_t partial_len,
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
status_t ghash_update(ghash_context_t *ctx, size_t input_len,
                      const uint8_t *input);

/**
 * Redundant version of ghash_update().
 *
 * Creates a copy of ctx and executes ghash_update() twice.
 * Compares the GHASH state stored in ctx after the redundant comparison.
 * The comparison is done on share s0 to avoid introducing SCA leakage.
 * If the comparison fails, trap.
 *
 * @param ctx Context object.
 * @param input_len Number of bytes in the input.
 * @param input Pointer to input buffer.
 */
status_t ghash_update_redundant(ghash_context_t *ctx, size_t input_len,
                                const uint8_t *input);

/**
 * Computes the correction terms needed for the masking scheme.
 *
 * correction_term0 = S0 * (H0 + 1).
 * correction_term1 = S0 * H1.
 * correction_term1_init = S1 * H1.
 *
 * @param enc_initial_counter_block0 Pointer to S0.
 * @param enc_initial_counter_block1 Pointer to S1.
 * @param ctx Context object.
 */
status_t ghash_handle_enc_initial_counter_block(
    const uint32_t *enc_initial_counter_block0,
    const uint32_t *enc_initial_counter_block1, ghash_context_t *ctx);

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
status_t ghash_final(ghash_context_t *ctx, uint32_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_GCM_GHASH_H_
